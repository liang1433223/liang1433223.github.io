'use strict';
/* =====================================================================
   云端会客厅 · 纯静态版
   无服务端：房间与消息全部走公共 MQTT over WebSocket。
   - 同时连 3 条公共通道；大厅条目广播到所有通道并标注房主所在通道，
     访客点房卡时自动切到房主通道再进房（消除多通道"分脑"）
   - 口令不落任何存储，只用来派生私有频道名（hash 后 16 位）
   - 房间内所有消息 AES-256-GCM 端到端加密，密钥 = 房号+口令派生，
     只存在于成员浏览器内存里，broker 与旁听者看到的全是密文
   - 大厅 = 房主定时重发的 retained 消息，新鲜度按本地接收时间判断
     （不比对房主时钟，免疫双方时钟偏差）
   - 聊天记录不 retain，晚进来的人天然看不到旧消息
   ===================================================================== */

/* ================= 常量 ================= */
const NS = 'yunduan7f3a';
const BROKERS = [
  'wss://broker-cn.emqx.io:8084/mqtt',
  'wss://broker.emqx.io:8084/mqtt',
  'wss://broker.hivemq.com:8884/mqtt',
];
const HB_MS = 4000;                    // 心跳间隔
const HOST_TIMEOUT_MS = 14000;         // 房主失联判定
const MEMBER_TTL_MS = 16000;           // 成员列表过期（本地接收时间）
const LOBBY_STALE_MS = 20000;          // 大厅条目过期（本地接收时间，房主 4s 一跳）
const JOIN_WAIT_MS = 2600;             // 握手等待
const TICK_MS = 2000;
const MAX_LEN = 500;

const NAMES = ['悟空', '哪吒', '敖丙', '嫦娥', '二郎神', '金蝉子', '太白金星', '镇元子',
  '牛魔王', '铁扇公主', '九尾狐', '白骨精', '东海龙王', '雷震子', '龟丞相', '红孩儿',
  '赤脚大仙', '玉兔', '司命星君', '风伯'];
const AVATARS = ['assets/monkey.jpg', 'assets/nezha.jpg'];
const RID_CHARS = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';

/* ================= 状态 ================= */
const S = {
  me: null,
  brokers: [],           // [{url, client, connected, connecting, retryTimer}]
  primary: 0,            // 房间流量走的通道（进房期间锁定）
  wantReconnect: true,
  waiters: [],

  roomId: null,
  roomName: '',
  pwHash: '',
  isHost: false,
  members: new Map(),
  lobby: new Map(),      // rid -> 条目 + _b(所在通道) + _ts(本地最近收到)
  lastHostTs: 0,
  hbTimer: null,
  tickTimer: null,
  pendingHere: null,
  pendingJoin: null,
  seq: 0,
  aesKey: null,          // 房间 AES-GCM 密钥（房号+口令派生，只在本页内存）
  cacheBye: null,        // 关页时同步发出的预加密告别包
  cacheLeave: null,
  decQueue: Promise.resolve(),
  _msig: '',
  _lsig: '',
};

/* ================= 小工具 ================= */
const $ = s => document.querySelector(s);
const $$ = s => [...document.querySelectorAll(s)];
const rand = (n, abc = RID_CHARS) => Array.from({ length: n }, () => abc[Math.floor(Math.random() * abc.length)]).join('');
const pick = a => a[Math.floor(Math.random() * a.length)];
const esc = s => String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));

let toastTimer;
function toast(msg, ms = 2600) {
  const t = $('#toast');
  t.textContent = msg;
  t.classList.add('on');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => t.classList.remove('on'), ms);
}
function show(view) {
  $$('.view').forEach(v => v.classList.remove('on'));
  $('#view-' + view).classList.add('on');
}

/* ================= 身份 ================= */
function newIdentity() {
  const id = 'u' + rand(12, 'abcdefghijkmnpqrstuvwxyz0123456789');
  const me = { id, name: pick(NAMES) + '·' + rand(2, '0123456789'), avatar: pick(AVATARS) };
  S.me = me;
  sessionStorage.setItem('wbme', JSON.stringify(me));
  applyIdentity();
  return me;
}
function applyIdentity() {
  $('#myAvatar').src = S.me.avatar;
  $('#myName').textContent = S.me.name;
  $('#barAvatar').src = S.me.avatar;
  $('#barName').textContent = S.me.name;
}

/* ================= 频道 ================= */
const T = {
  lobby: rid => `${NS}/lobby/${rid}`,
  ctrl: (rid, h) => `${NS}/r/${rid}/${h}/c`,
  msg: (rid, h) => `${NS}/r/${rid}/${h}/m`,
};

/* 口令 → 频道后缀。只在本地算，不上传明文。 */
async function pwhash(rid, pass) {
  const raw = rid + '|' + pass;
  try {
    if (crypto && crypto.subtle) {
      const d = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(raw));
      return [...new Uint8Array(d)].slice(0, 8).map(b => b.toString(16).padStart(2, '0')).join('');
    }
  } catch (_) { /* 非安全上下文时退化 */ }
  let h1 = 0x811c9dc5, h2 = 0x1000193;
  for (let i = 0; i < raw.length; i++) {
    h1 = (h1 ^ raw.charCodeAt(i)) * 0x01000193 >>> 0;
    h2 = (h2 + raw.charCodeAt(i) * (i + 7)) * 0x85ebca6b >>> 0;
  }
  return (h1.toString(16) + h2.toString(16)).padEnd(16, '0').slice(0, 16);
}

/* ---------- 端到端加密（AES-256-GCM） ---------- */
function b64(u8) { let s = ''; for (let i = 0; i < u8.length; i++) s += String.fromCharCode(u8[i]); return btoa(s); }
function unb64(str) { const b = atob(str), u = new Uint8Array(b.length); for (let i = 0; i < b.length; i++) u[i] = b.charCodeAt(i); return u; }

/* 房间密钥与频道哈希域分离，即便频道名公开也无法推回密钥 */
async function deriveRoomKey(rid, pass) {
  try {
    if (!crypto || !crypto.subtle) return null;
    const seed = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(`${rid}|${pass}|aes|${NS}`));
    return await crypto.subtle.importKey('raw', seed, 'AES-GCM', false, ['encrypt', 'decrypt']);
  } catch (_) { return null; }
}

/* 有密钥则加密为 {iv,d}，无密钥（非安全上下文）退化为明文 */
async function encJSON(o) {
  if (!S.aesKey) return JSON.stringify(o);
  const iv = crypto.getRandomValues(new Uint8Array(12));
  const ct = await crypto.subtle.encrypt({ name: 'AES-GCM', iv }, S.aesKey, new TextEncoder().encode(JSON.stringify(o)));
  return JSON.stringify({ iv: b64(iv), d: b64(new Uint8Array(ct)) });
}

/* 收包：优先解密；解不开再按明文兜底（兼容无加密能力的发送方）；都失败返回 null */
async function decPayload(text) {
  if (S.aesKey) {
    try {
      const w = JSON.parse(text);
      if (w && typeof w === 'object' && 'iv' in w && 'd' in w) {
        const pt = await crypto.subtle.decrypt({ name: 'AES-GCM', iv: unb64(w.iv) }, S.aesKey, unb64(w.d));
        return JSON.parse(new TextDecoder().decode(pt));
      }
      return w;
    } catch (_) { return null; }
  }
  try { return JSON.parse(text); } catch (_) { return null; }
}

/* ================= 多通道连接 ================= */
function setConn() {
  const el = $('#connState');
  if (!el) return;
  const total = S.brokers.length;
  const n = S.brokers.filter(b => b.connected).length;
  const prim = S.brokers[S.primary] && S.brokers[S.primary].connected;
  let txt, color;
  if (prim && n === total) { txt = '● 云路已通'; color = 'var(--teal)'; }
  else if (prim) { txt = `● 云路已通 ${n}/${total}`; color = 'var(--teal)'; }
  else if (n > 0) { txt = `○ 备用云路 ${n}/${total}`; color = 'var(--gold2)'; }
  else { txt = '● 云路已断'; color = '#e8836f'; }
  el.textContent = txt;
  el.setAttribute('style', `color:${color};background:transparent;border-color:rgba(255,255,255,.12)`);
  renderLobby();   // 断线状态会体现在大厅提示上
}

function connectBroker(bi) {
  const b = S.brokers[bi];
  if (b.connecting || b.connected) return;
  b.connecting = true;
  setConn();
  let c;
  try {
    c = mqtt.connect(b.url, {
      clientId: 'wbc_' + rand(14, 'abcdefghijkmnpqrstuvwxyz0123456789'),
      clean: true, keepalive: 25, connectTimeout: 8000,
      reconnectPeriod: 0, protocolVersion: 4,
    });
  } catch (_) {
    b.connecting = false;
    scheduleRetry(bi);
    return;
  }
  b.client = c;
  let settled = false;
  const guard = setTimeout(() => {
    if (settled) return;
    settled = true;
    b.connecting = false;
    try { c.end(true); } catch (_) {}
    scheduleRetry(bi);
  }, 9000);

  c.on('connect', () => {
    clearTimeout(guard);
    settled = true;
    b.connecting = false;
    b.connected = true;
    onBrokerConnected(bi);
    maybeReassignPrimary();
    flushWaiters();
    setConn();
  });

  c.on('error', () => { /* 交给 close / guard 处理 */ });

  c.on('close', () => {
    b.connected = false;
    b.connecting = false;
    if (!settled) {
      settled = true;
      clearTimeout(guard);
      scheduleRetry(bi);
      setConn();
      return;
    }
    setConn();
    maybeReassignPrimary();
    if (S.wantReconnect) scheduleRetry(bi);
  });

  c.on('message', (topic, buf, packet) => onMessage(bi, topic, buf, packet));
}

function scheduleRetry(bi) {
  const b = S.brokers[bi];
  if (!S.wantReconnect || b.retryTimer) return;
  b.retryTimer = setTimeout(() => { b.retryTimer = null; connectBroker(bi); }, 2500 + bi * 800);
}

/* 不在房间里时，若主通道挂了就把最先连上的通道提为主 */
function maybeReassignPrimary() {
  if (S.roomId) return;
  if (S.brokers[S.primary] && S.brokers[S.primary].connected) return;
  const ok = S.brokers.findIndex(b => b.connected);
  if (ok >= 0 && ok !== S.primary) S.primary = ok;
}

function onBrokerConnected(bi) {
  const b = S.brokers[bi];
  try { b.client.subscribe(NS + '/lobby/+', { qos: 1 }); } catch (_) {}
  if (bi === S.primary && S.roomId && S.pwHash) {
    try { b.client.subscribe([T.ctrl(S.roomId, S.pwHash), T.msg(S.roomId, S.pwHash)], { qos: 1 }); } catch (_) {}
    S.lastHostTs = Date.now();
    if (S.isHost) publishLobby();
    else publishCtrl({ k: 'hello' }, 0);   // 断线重连后重新敲门，确认房主还在
  }
}

function ensureConnected() {
  if (S.brokers[S.primary] && S.brokers[S.primary].connected) return Promise.resolve(true);
  return new Promise(resolve => {
    S.waiters.push(resolve);
    setTimeout(() => resolve(!!(S.brokers[S.primary] && S.brokers[S.primary].connected)), 12000);
  });
}
function flushWaiters() {
  const primOk = !!(S.brokers[S.primary] && S.brokers[S.primary].connected);
  S.waiters.splice(0).forEach(fn => fn(primOk));
}

function primaryClient() {
  const b = S.brokers[S.primary];
  return b && b.connected ? b.client : null;
}

/* ================= 收消息 ================= */
function onMessage(bi, topic, buf, packet) {
  const text = buf ? buf.toString() : '';

  if (topic.startsWith(NS + '/lobby/')) {
    const rid = topic.slice(NS.length + 7);
    if (!text) {
      if (S.lobby.delete(rid)) renderLobby();
      return;
    }
    let o; try { o = JSON.parse(text); } catch (_) { return; }
    if (o && o.r === rid) {
      o._b = (typeof o.b === 'number' && S.brokers[o.b]) ? o.b : bi;   // 记住房主在哪条通道
      o._ts = Date.now();                                               // 新鲜度用本地时钟，免疫双方时钟偏差
      const cur = S.lobby.get(rid);
      // 订阅瞬间收到的 retained 是"历史值"，房主可能早已离开 → 先标记为待确认。
      // 注意：同一份历史值会在多条通道上各来一次，所以不能用"收到次数"判断，
      // 只能用 ①非 retained 的实时推送（房主每 4s 一跳）②同一通道连续 3 次推送（兜底）。
      const same = cur && cur._hb === bi;
      o._hb = bi;
      o._hc = (same ? (cur._hc || 1) : 0) + 1;
      o._live = (!packet || packet.retain !== true || o._hc >= 3) ? 1 : 0;
      if (cur && cur._live) o._live = 1;
      if (!cur || (o.t || 0) >= (cur.t || 0)) S.lobby.set(rid, o);
      else if (cur && o._live) cur._live = 1;
      renderLobby();
    }
    return;
  }

  if (!S.roomId || !text || bi !== S.primary) return;

  if (topic.endsWith('/c') || topic.endsWith('/m')) {
    // 解密是异步的，排队保序，防止消息乱序渲染
    S.decQueue = S.decQueue.then(async () => {
      const o = await decPayload(text);
      if (!o || !S.roomId || o.r !== S.roomId) return;
      if (topic.endsWith('/c')) onCtrl(o);
      else onChat(o);
    }).catch(() => {});
    return;
  }
}

function onCtrl(o) {
  const now = Date.now();
  switch (o.k) {
    case 'hello':
      if (S.isHost) publishCtrl({ k: 'here', h: 1 }, 1);
      break;
    case 'here':
      S.lastHostTs = now;
      touch(o, 1);
      if (S.pendingHere) S.pendingHere();
      break;
    case 'join':
      touch(o, 0);
      pushSys(`${o.n} 进来了`);
      break;
    case 'leave':
      if (S.members.delete(o.f)) {
        renderMembers();
        pushSys(`${o.n} 离开了`);
      }
      break;
    case 'bye':
      if (!S.isHost) kicked('房主已散场，会客厅随之消散');
      break;
    case 'hb':
      if (o.h) S.lastHostTs = now;
      touch(o, o.h ? 1 : 0);
      break;
  }
}

function onChat(o) {
  if (!o.i) return;
  if (o.f === S.me.id) return;                 // 自己发的已本地渲染
  if (o.img) {
    addImgBubble({ name: o.n || '客', avatar: o.a || AVATARS[0], src: o.img, self: false });
  } else if (o.x) {
    addBubble({ name: o.n || '客', avatar: o.a || AVATARS[0], text: o.x, self: false });
  }
}

/* ================= 发消息（房间内全部走密文） ================= */
async function publishCtrl(o, qos = 0) {
  const c = primaryClient();
  if (!c || !S.roomId) return;
  const topic = T.ctrl(S.roomId, S.pwHash);   // await 期间状态可能被清空，先锁定频道
  const payload = Object.assign({
    r: S.roomId, f: S.me.id, n: S.me.name, a: S.me.avatar, t: Date.now(),
  }, o);
  const body = await encJSON(payload);
  try { c.publish(topic, body, { qos }); } catch (_) {}
}

/* 大厅条目广播到所有通道，并标注自己所在的通道号 */
function publishLobby() {
  if (!S.isHost || !S.roomId) return;
  const now = Date.now();
  const alive = [...S.members.values()].filter(m => now - m.ts < MEMBER_TTL_MS).length;
  const payload = JSON.stringify({ r: S.roomId, n: S.roomName, h: S.me.name, c: Math.max(alive, 1), t: now, b: S.primary });
  for (const b of S.brokers) {
    if (!b.connected) continue;
    try { b.client.publish(T.lobby(S.roomId), payload, { qos: 0, retain: true }); } catch (_) {}
  }
}

async function sendMessage(text) {
  if (!S.roomId) return;
  const c = primaryClient();
  if (!c) { toast('云路未通，消息发不出去'); return; }
  const topic = T.msg(S.roomId, S.pwHash);    // 同上，先锁定频道
  const payload = {
    r: S.roomId, i: S.me.id + ':' + (++S.seq), f: S.me.id,
    n: S.me.name, a: S.me.avatar, x: text, t: Date.now(),
  };
  try {
    const body = await encJSON(payload);
    c.publish(topic, body, { qos: 1 });
  } catch (_) {
    toast('发送失败');
    return;
  }
  addBubble({ name: S.me.name, avatar: S.me.avatar, text, self: true });
}

/* ================= 图片消息 ================= */
const IMG_MAX_SIDE = 1280;          // 压缩后最长边
const IMG_TARGET_B64 = 200 * 1024;  // 单图 base64 上限（密文≈1.4 倍，仍远低于 broker 包上限）
const IMG_HARD_LIMIT = 380 * 1024;

function loadImgEl(url) {
  return new Promise((resolve, reject) => {
    const im = new Image();
    im.onload = () => resolve(im);
    im.onerror = () => reject(new Error('图片解析失败'));
    im.src = url;
  });
}

/* 浏览器端压缩：等比缩放 + JPEG 质量递减，保证密文包不超过 broker 限制 */
async function compressImage(file) {
  if (!/^image\//.test(file.type)) throw new Error('请选择图片文件');
  if (file.size > 20 * 1024 * 1024) throw new Error('图片过大（限 20MB 原图）');
  const url = URL.createObjectURL(file);
  let img;
  try { img = await loadImgEl(url); } finally { setTimeout(() => URL.revokeObjectURL(url), 0); }

  let w = img.naturalWidth || img.width;
  let h = img.naturalHeight || img.height;
  if (!w || !h) throw new Error('图片尺寸读取失败');

  const draw = (ww, hh) => {
    const cv = document.createElement('canvas');
    cv.width = ww; cv.height = hh;
    const ctx = cv.getContext('2d');
    ctx.fillStyle = '#0a0d18';                     // 透明 PNG 不留黑块
    ctx.fillRect(0, 0, ww, hh);
    ctx.drawImage(img, 0, 0, ww, hh);
    return cv;
  };

  let side = IMG_MAX_SIDE;
  for (let attempt = 0; attempt < 4; attempt++) {
    const scale = Math.min(1, side / Math.max(w, h));
    const ww = Math.max(1, Math.round(w * scale));
    const hh = Math.max(1, Math.round(h * scale));
    const cv = draw(ww, hh);
    let q = 0.82;
    let data = cv.toDataURL('image/jpeg', q);
    while (data.length > IMG_TARGET_B64 && q > 0.42) {
      q -= 0.12;
      data = cv.toDataURL('image/jpeg', q);
    }
    if (data.length <= IMG_TARGET_B64 || attempt === 3) {
      if (data.length > IMG_HARD_LIMIT) throw new Error('图片压不下去，换张小的吧');
      return data;
    }
    side = Math.round(side * 0.72);                 // 还是太大 → 缩尺寸再来
  }
}

async function sendImage(dataUrl) {
  if (!S.roomId || !dataUrl) return;
  const c = primaryClient();
  if (!c) { toast('云路未通，消息发不出去'); return; }
  const topic = T.msg(S.roomId, S.pwHash);
  const payload = {
    r: S.roomId, i: S.me.id + ':' + (++S.seq), f: S.me.id,
    n: S.me.name, a: S.me.avatar, img: dataUrl, t: Date.now(),
  };
  try {
    const body = await encJSON(payload);   // 图片与文字同一条密文通道，broker 只看到 {iv,d}
    await new Promise(res => c.publish(topic, body, { qos: 1 }, () => res()));
  } catch (_) {
    toast('图片发送失败');
    return;
  }
  addImgBubble({ name: S.me.name, avatar: S.me.avatar, src: dataUrl, self: true });
}

async function pickAndSendImage(file) {
  const btn = $('#btnImg');
  if (!file || !S.roomId) return;
  try {
    btn.disabled = true; btn.classList.add('sending');
    toast('正在压缩图片…', 1200);
    const dataUrl = await compressImage(file);
    await sendImage(dataUrl);
  } catch (e) {
    toast(e.message || '图片处理失败', 2600);
  } finally {
    btn.disabled = false; btn.classList.remove('sending');
    if ($('#fileImg')) $('#fileImg').value = '';
  }
}

/* ================= 房间生命周期 ================= */
async function enterRoom(rid, name, pass, isHost) {
  if (S.roomId) hardLeave(false);
  const pwHash = await pwhash(rid, pass);
  S.aesKey = await deriveRoomKey(rid, pass);   // 同一口令，独立派生加密密钥
  const ok = await ensureConnected();
  if (!ok) { toast('云路未通，稍后再试'); return false; }

  S.roomId = rid;
  S.roomName = name;
  S.pwHash = pwHash;
  S.isHost = isHost;
  S.members.clear();
  S._msig = '';
  S.lastHostTs = Date.now();
  S.seq = 0;
  $('#chat').innerHTML = '';
  $('#roomName').textContent = name;
  $('#roomSub').textContent = `${isHost ? '你是房主 · 离开即散场' : '凭口令进入'} · 房号 ${rid}`;
  show('room');

  const granted = await subscribeRoomTopics();
  if (!granted) {
    toast('频道订阅失败，换个网络再试');
    hardLeave(false);
    show('lobby');
    return false;
  }

  startTimers();
  const self = { id: S.me.id, n: S.me.name, a: S.me.avatar, h: isHost ? 1 : 0, ts: Date.now() };
  S.members.set(S.me.id, self);

  // 预加密关页用的告别包：pagehide 里只能同步发送，来不及等异步加密
  if (S.aesKey) {
    const wrap = o => encJSON(Object.assign({ r: rid, f: S.me.id, n: S.me.name, t: Date.now() }, o));
    S.cacheBye = await wrap({ k: 'bye' });
    S.cacheLeave = await wrap({ k: 'leave' });
  } else {
    S.cacheBye = null;
    S.cacheLeave = null;
  }

  if (isHost) {
    renderMembers();
    publishLobby();
    await publishCtrl({ k: 'join', h: 1 }, 1);
    pushSys(`会客厅已开辟 · 房号 ${rid}，把房号与口令告诉朋友`);
    return true;
  }

  // 敲门：房主收到 hello 才会回 here，以此校验口令（口令错 → 频道不同 → 无人应答）
  await publishCtrl({ k: 'hello' }, 1);
  const okHere = await waitHere(JOIN_WAIT_MS);
  if (!okHere) {
    try { primaryClient() && primaryClient().unsubscribe([T.ctrl(rid, pwHash), T.msg(rid, pwHash)]); } catch (_) {}
    hardLeave(false);
    show('lobby');
    toast('口令不对，或这间会客厅已散场', 3000);
    return false;
  }

  S.lastHostTs = Date.now();
  renderMembers();
  await publishCtrl({ k: 'join' }, 1);
  pushSys(`凭口令入席 · 房号 ${rid}`);
  return true;
}

function subscribeRoomTopics() {
  return new Promise(resolve => {
    const b = S.brokers[S.primary];
    if (!b || !b.connected) return resolve(false);
    let done = false;
    const fin = v => { if (!done) { done = true; resolve(v); } };
    setTimeout(() => fin(false), 6000);
    b.client.subscribe([T.ctrl(S.roomId, S.pwHash), T.msg(S.roomId, S.pwHash)], { qos: 1 }, (err) => fin(!err));
  });
}

function waitHere(ms) {
  return new Promise(resolve => {
    let done = false;
    const fin = v => {
      if (done) return;
      done = true;
      S.pendingHere = null;
      clearTimeout(t);
      resolve(v);
    };
    const t = setTimeout(() => fin(false), ms);
    S.pendingHere = () => fin(true);
  });
}

function hardLeave(notify) {
  if (!S.roomId) return;
  const rid = S.roomId;
  if (notify) {
    if (S.isHost) {
      publishCtrl({ k: 'bye' }, 1);
      clearLobbyEntry(rid);
    } else {
      publishCtrl({ k: 'leave' }, 1);
    }
  }
  const c = primaryClient();
  if (c) {
    try { c.unsubscribe([T.ctrl(rid, S.pwHash), T.msg(rid, S.pwHash)]); } catch (_) {}
  }
  clearInterval(S.hbTimer); S.hbTimer = null;
  clearInterval(S.tickTimer); S.tickTimer = null;
  S.roomId = null; S.roomName = ''; S.pwHash = ''; S.isHost = false;
  S.members.clear(); S._msig = ''; S.pendingHere = null;
  S.aesKey = null; S.cacheBye = null; S.cacheLeave = null;
  S.decQueue = Promise.resolve();
  $('#chat').innerHTML = '';
}

/* 清掉大厅 retained 条目：所有通道一起清 */
function clearLobbyEntry(rid) {
  S.lobby.delete(rid);
  for (const b of S.brokers) {
    if (!b.connected) continue;
    try { b.client.publish(T.lobby(rid), '', { retain: true, qos: 0 }); } catch (_) {}
  }
}

/* 页面内确认框（原生 confirm 在 WebView/iframe 里会被静默屏蔽，返回 false） */
function uiConfirm(title, text, okText, cancelText) {
  return new Promise(resolve => {
    const mask = $('#maskConfirm');
    $('#confirmTitle').textContent = title;
    $('#confirmText').textContent = text;
    $('#btnConfirmOk').textContent = okText || '确定';
    $('#btnConfirmCancel').textContent = cancelText || '取消';
    mask.classList.add('on');
    const done = v => {
      mask.classList.remove('on');
      $('#btnConfirmOk').onclick = null;
      $('#btnConfirmCancel').onclick = null;
      mask.onclick = null;
      resolve(v);
    };
    $('#btnConfirmOk').onclick = () => done(true);
    $('#btnConfirmCancel').onclick = () => done(false);
    mask.onclick = e => { if (e.target === mask) done(false); };
  });
}

function leaveToLobby(notify) {
  doLeave(notify);
}

async function doLeave(notify) {
  if (!S.roomId) return;
  const wasHost = S.isHost;
  if (wasHost && notify) {
    const ok = await uiConfirm('确认离开？',
      '你是房主 —— 你一走，会客厅立即散场，所有人都得离开。',
      '确定离开', '先留一会儿');
    if (!ok || !S.roomId) return;   // 等待期间可能已被踢出/散场
  }
  hardLeave(notify);
  show('lobby');
  renderLobby();
  if (notify) toast(wasHost ? '会客厅已散场，旧语随云散去' : '已离开 · 再进来时，旧消息不会重现');
}

function kicked(reason) {
  toast(reason, 3400);
  hardLeave(false);
  show('lobby');
  renderLobby();
}

function startTimers() {
  clearInterval(S.hbTimer); clearInterval(S.tickTimer);
  S.hbTimer = setInterval(heartbeat, HB_MS);
  S.tickTimer = setInterval(tick, TICK_MS);
}

function heartbeat() {
  if (!S.roomId) return;
  const me = S.members.get(S.me.id);
  if (me) me.ts = Date.now();
  publishCtrl({ k: 'hb', h: S.isHost ? 1 : 0 }, 0);
  if (S.isHost) publishLobby();
}

function tick() {
  const now = Date.now();

  if (S.roomId) {
    let dirty = false;
    for (const [id, m] of S.members) {
      if (id === S.me.id) continue;
      if (now - m.ts > MEMBER_TTL_MS) { S.members.delete(id); dirty = true; }
    }
    if (dirty) renderMembers();

    if (!S.isHost && now - S.lastHostTs > HOST_TIMEOUT_MS) {
      kicked('房主已失联，会客厅散场');
      return;
    }
  }

  // 大厅：过期条目清掉（自愈），顺便清理通道上的 retained 幽灵
  let changed = false;
  for (const [rid, v] of [...S.lobby]) {
    const untrusted = !v._live;
    const ttl = untrusted ? Math.min(LOBBY_STALE_MS, 9000) : LOBBY_STALE_MS;
    if (now - (v._ts || 0) > ttl) {
      S.lobby.delete(rid);
      for (const b of S.brokers) {
        if (!b.connected) continue;
        try { b.client.publish(T.lobby(rid), '', { retain: true, qos: 0 }); } catch (_) {}
      }
      changed = true;
    }
  }
  if (changed) renderLobby();
  else if (S._lobbyForceRender) { S._lobbyForceRender = false; renderLobby(); }
}

/* ================= 渲染 ================= */
function touch(o, hostFlag) {
  if (!o || !o.f) return;
  if (o.f === S.me.id) {
    const me = S.members.get(S.me.id);
    if (me) { me.ts = Date.now(); if (hostFlag) me.h = 1; }
    return;
  }
  const cur = S.members.get(o.f);
  S.members.set(o.f, {
    id: o.f,
    n: o.n || (cur && cur.n) || '客',
    a: o.a || (cur && cur.a) || AVATARS[0],
    h: hostFlag ? 1 : (cur ? cur.h : 0),
    ts: Date.now(),
  });
  renderMembers();
}

function renderMembers() {
  const now = Date.now();
  const arr = [...S.members.values()]
    .filter(m => now - m.ts < MEMBER_TTL_MS || m.id === S.me.id)
    .sort((a, b) => (b.h || 0) - (a.h || 0));
  const sig = arr.map(m => m.id + m.n + (m.h ? '1' : '0')).join('|');
  $('#roomSub').textContent = `${arr.length} 人在此 · 房号 ${S.roomId || ''}${S.isHost ? ' · 你是房主' : ''}`;
  if (sig === S._msig) return;
  S._msig = sig;
  $('#memberList').innerHTML = arr.map(m => `
    <span class="mchip" title="${m.h ? '房主' : '成员'}">
      <img src="${esc(m.a)}" alt=""><span>${esc(m.n)}${m.h ? ' <span class="crown">👑</span>' : ''}</span>
    </span>`).join('');
}

function pushSys(text) {
  const chat = $('#chat');
  const near = chat.scrollHeight - chat.scrollTop - chat.clientHeight < 140;
  const div = document.createElement('div');
  div.className = 'msg sys';
  div.innerHTML = `<div class="bubble">— ${esc(text)} —</div>`;
  chat.appendChild(div);
  if (near) chat.scrollTop = chat.scrollHeight;
}

function addBubble(m) {
  const chat = $('#chat');
  const near = chat.scrollHeight - chat.scrollTop - chat.clientHeight < 140;
  const div = document.createElement('div');
  div.className = 'msg' + (m.self ? ' self' : '');
  div.innerHTML = `
    <img class="av" src="${esc(m.avatar)}" alt="">
    <div class="body">
      <div class="who"><span>${esc(m.name)}</span></div>
      <div class="bubble">${esc(m.text)}</div>
    </div>`;
  chat.appendChild(div);
  if (near || m.self) chat.scrollTop = chat.scrollHeight;
}

function addImgBubble(m) {
  const chat = $('#chat');
  const near = chat.scrollHeight - chat.scrollTop - chat.clientHeight < 140;
  const div = document.createElement('div');
  div.className = 'msg' + (m.self ? ' self' : '');
  div.innerHTML = `
    <img class="av" src="${esc(m.avatar)}" alt="">
    <div class="body">
      <div class="who"><span>${esc(m.name)}</span></div>
      <div class="bubble img"><img src="${esc(m.src)}" alt="图片" loading="lazy"></div>
    </div>`;
  const pic = div.querySelector('.bubble.img img');
  if (pic) pic.onclick = () => openLightbox(m.src);
  chat.appendChild(div);
  if (near || m.self) chat.scrollTop = chat.scrollHeight;
}

function openLightbox(src) {
  const lb = $('#lightbox');
  if (!lb) return;
  lb.querySelector('img').src = src;
  lb.classList.add('on');
}

function closeLightbox() {
  const lb = $('#lightbox');
  if (!lb) return;
  lb.classList.remove('on');
  lb.querySelector('img').src = '';
}

function renderLobby() {
  const now = Date.now();
  const anyConn = S.brokers.some(b => b.connected);
  const rooms = [...S.lobby.values()]
    .filter(r => r && r.r && r._live && now - (r._ts || 0) < LOBBY_STALE_MS)
    .sort((a, b) => (b.t || 0) - (a.t || 0));

  if ($('#lobbyCnt')) $('#lobbyCnt').textContent = rooms.length;
  if ($('#roomCnt')) $('#roomCnt').textContent = rooms.length + ' 间';

  const sig = (anyConn ? '1' : '0') + '|' + rooms.map(r => r.r + r.n + r.h + r.c + (r._b || 0)).join('|');
  if (sig === S._lsig) return;
  S._lsig = sig;

  const el = $('#roomList');
  if (!anyConn) {
    el.innerHTML = `<div class="empty"><div class="big">🌫️</div>云路未通，暂时看不见任何会客厅<br><span class="tiny">正在自动重连多条云路…（顶部有状态）</span></div>`;
    return;
  }
  if (!rooms.length) {
    el.innerHTML = `<div class="empty"><div class="big">🍃</div>云海空空，一间会客厅都没有<br><span class="tiny">做第一个开辟的人吧</span></div>`;
    return;
  }
  el.innerHTML = rooms.map(r => `
    <div class="room-card" data-id="${esc(r.r)}">
      <span class="lock">🔒</span>
      <div>
        <div class="rname">${esc(r.n)}</div>
        <div class="meta">
          <span>房主 ${esc(r.h)}</span>
          <span>${Number(r.c) || 1} 人</span>
          <span>房号 ${esc(r.r)}</span>
        </div>
      </div>
      <span class="arrow">›</span>
    </div>`).join('');
}

/* ================= 交互绑定 ================= */
function bindIdentityUI() {
  $('#btnReroll').onclick = () => { newIdentity(); toast('已换一具化身'); };
  $('#btnEnter').onclick = () => {
    if (!S.me) return;
    applyIdentity();
    show('lobby');
    renderLobby();
    if (!S.brokers.some(b => b.connected)) ensureConnected();
  };
  $('#btnLogout').onclick = () => {
    if (S.roomId) hardLeave(true);
    S.me = null;
    sessionStorage.removeItem('wbme');
    newIdentity();
    show('enter');
  };
}

function bindLobbyUI() {
  $('#btnOpenCreate').onclick = () => {
    if (!S.brokers[S.primary] || !S.brokers[S.primary].connected) toast('云路还在连，稍等一下');
    $('#createName').value = '';
    $('#createPass').value = '';
    $('#maskCreate').classList.add('on');
    setTimeout(() => $('#createName').focus(), 60);
  };
  $('#btnCreateCancel').onclick = () => $('#maskCreate').classList.remove('on');
  $('#btnJoinCancel').onclick = () => $('#maskJoin').classList.remove('on');

  $('#btnCreateOk').onclick = async () => {
    const name = $('#createName').value.trim();
    const pass = $('#createPass').value;
    if (!name) return toast('先给会客厅起个名字');
    if (pass.length < 4) return toast('口令至少 4 位');

    let rid;
    do { rid = rand(6); } while (S.lobby.has(rid));

    const ok = await enterRoom(rid, name, pass, true);
    if (ok) $('#maskCreate').classList.remove('on');
  };

  $('#btnJoinOk').onclick = async () => {
    const pass = $('#joinPass').value;
    if (!pass) return toast('请输入口令');
    const pj = S.pendingJoin;
    if (!pj) return;
    const ok = await enterRoom(pj.rid, pj.name, pass, false);
    if (ok) $('#maskJoin').classList.remove('on');
  };

  $('#roomList').addEventListener('click', e => {
    const card = e.target.closest('.room-card');
    if (!card) return;
    const rid = card.dataset.id;
    const r = S.lobby.get(rid);
    if (!r) return toast('这间会客厅刚刚散场了');
    // 房主在别的通道上 → 先切过去再敲门（大厅是全通道广播的，房间不是）
    if (r._b !== S.primary && !S.roomId) {
      const b = S.brokers[r._b];
      if (!b || !b.connected) return toast('房主所在的云路暂时连不上，稍后再试');
      S.primary = r._b;
    }
    S.pendingJoin = { rid, name: r.n };
    $('#joinRoomName').textContent = r.n;
    $('#joinPass').value = '';
    $('#maskJoin').classList.add('on');
    setTimeout(() => $('#joinPass').focus(), 60);
  });

  $('#joinPass').addEventListener('keydown', e => { if (e.key === 'Enter') $('#btnJoinOk').click(); });
  $('#createPass').addEventListener('keydown', e => { if (e.key === 'Enter') $('#btnCreateOk').click(); });
}

function bindRoomUI() {
  $('#btnLeave').onclick = () => leaveToLobby(true);

  const send = () => {
    const input = $('#msgInput');
    const text = input.value.trim().slice(0, MAX_LEN);
    if (!text || !S.roomId) return;
    input.value = '';
    sendMessage(text);
  };
  $('#btnSend').onclick = send;
  $('#msgInput').addEventListener('keydown', e => {
    if (e.key === 'Enter' && !e.shiftKey) { e.preventDefault(); send(); }
  });

  // 图片：点按钮唤起文件选择；支持直接粘贴图片
  $('#btnImg').onclick = () => { if (S.roomId) $('#fileImg').click(); };
  $('#fileImg').addEventListener('change', e => {
    const f = e.target.files && e.target.files[0];
    if (f) pickAndSendImage(f);
  });
  $('#msgInput').addEventListener('paste', e => {
    if (!S.roomId) return;
    const items = (e.clipboardData && e.clipboardData.items) || [];
    for (const it of items) {
      if (it.kind === 'file' && /^image\//.test(it.type)) {
        const f = it.getAsFile();
        if (f) { e.preventDefault(); pickAndSendImage(f); }
        return;
      }
    }
  });
  const lb = $('#lightbox');
  if (lb) lb.onclick = closeLightbox;
  window.addEventListener('keydown', e => { if (e.key === 'Escape') closeLightbox(); });

  window.addEventListener('pagehide', () => {
    if (!S.roomId) return;
    const b = S.brokers[S.primary];
    if (!b || !b.connected) return;
    const cache = S.isHost ? S.cacheBye : S.cacheLeave;
    if (cache) {
      // 用预先加密好的包同步发出，关页前一定来得及
      try { b.client.publish(T.ctrl(S.roomId, S.pwHash), cache, { qos: 0 }); } catch (_) {}
    } else {
      publishCtrl({ k: S.isHost ? 'bye' : 'leave' }, 0);
    }
    if (S.isHost) clearLobbyEntry(S.roomId);
  });

  window.addEventListener('online', () => { S.brokers.forEach((_, i) => { if (!S.brokers[i].connected) scheduleRetry(i); }); });
}

/* ================= 启动 ================= */
(function init() {
  bindIdentityUI();
  bindLobbyUI();
  bindRoomUI();

  let saved = null;
  try { saved = JSON.parse(sessionStorage.getItem('wbme') || 'null'); } catch (_) {}
  if (saved && saved.id && saved.name && saved.avatar) {
    S.me = saved;
    applyIdentity();
  } else {
    newIdentity();
  }

  S.brokers = BROKERS.map(url => ({ url, client: null, connected: false, connecting: false, retryTimer: null }));
  setConn();
  renderLobby();
  S.brokers.forEach((_, i) => connectBroker(i));
})();

/*! hs-game.js 3.2.4 — the HS TikTok SDK for native TikTok mini games.
 *
 * Put this file and hs-sdk.min.js next to your game.js, then:
 *
 *   var HSGame = require('./hs-game.js');
 *   HSGame.start({
 *     gameId: '...', sdkKey: 'sk_live_...',
 *     defaults: { rewards: {...}, items: {...} },     // the game's own reward table
 *     onGive: function (items, from) { ... },         // THE place anything is given
 *     onLoad: function (cloud) { ... }                // cloud save from another phone
 *   });
 *
 *   HSGame.claim('mission_a')        // a game moment completed → its reward goes to onGive
 *   HSGame.showAd('revive')          // ad at a place → reward (if any) goes to onGive
 *   HSGame.share({ title })          // share → the "share" reward goes to onGive
 *   HSGame.save(progress)            // cloud save
 *   HSGame.shop() / HSGame.buy(id)   // purchases → onGive
 *   HSGame.has('share')              // show a button only where it works (see has())
 *   HSGame.on('pause' | 'resume')    // mute + freeze while an ad / purchase / the app is away
 *
 * One game, two platforms: TikTok Minis, and the HS Android app (the same
 * files in a WebView, packed by HS). The game never checks the platform —
 * HSGame.has() says what is on, and the ad provider is HS's choice.
 *
 * Data-driven: a reward key, an ad place, an item, a product — if it is in the
 * HS dashboard (or the game's defaults), it works; if not, nothing happens.
 *
 * Rules this file enforces so a game cannot get them wrong:
 *   - It never throws, and runs without the SDK or credentials (rewards then
 *     come from the defaults; ads, shop and cloud are simply off).
 *   - Rewards reach the game ONLY through onGive. If onGive throws, nothing is
 *     recorded: a claim can be made again, a paid order comes back next login.
 *   - An ad reward only for a completed ad; a share reward only for a share.
 *   - A fresh install never overwrites the cloud.
 *
 * Needs hs-sdk.min.js 1.1.1 or newer (the Android app needs it — device
 * accounts and Google Play purchases; TikTok works with 1.0.7+, also under its
 * old name hs-tiktok-sdk.min.js). With 1.1.2 a change not yet in the cloud
 * survives an app killed before the sync, and paid orders are confirmed only
 * once their save is in the cloud; an older SDK works as before 3.2.3.
 */
(function (root) {
  'use strict';

  var VERSION = '3.2.4';
  // The SDK waits for the ad's own answer; past this the ad counts as failed,
  // so a host that never answers cannot latch or freeze the game. Android:
  // longer than the app's own ad watchdog (120 s), so there the app answers
  // first. TikTok: the SDK gives up on an ad that does not load in 8 s, so
  // this only ever waits for an ad on screen that sends no close (60 s; a
  // late close still pays the reward).
  var AD_STALE_MS_ANDROID = 130000;
  var AD_STALE_MS_TIKTOK = 60000;
  function adStaleMs() { return platformName() === 'android' ? AD_STALE_MS_ANDROID : AD_STALE_MS_TIKTOK; }
  var AD_TAP_MS = 8000; // an ad not under way this long after the tap is dropped (the SDK's load cap too)
  var BUY_PAUSE_MAX_MS = 120000; // the game unfreezes behind a pay sheet that stays open longer
  var TIKTOK_KEYS = { tiktok_shortcut: 'shortcut', tiktok_profile: 'profile' };
  var BUILTIN_LIMIT = { share: 'daily', tiktok_shortcut: 'once', tiktok_profile: 'once' };

  var sdk = null;
  var loadError = '';
  if (typeof require === 'function') {
    try {
      sdk = require('./hs-sdk.min.js');
    } catch (e) {
      // A game folder from before 1.1 has the SDK under its old name.
      try { sdk = require('./hs-tiktok-sdk.min.js'); } catch (e2) { loadError = 'hs-sdk.min.js not found next to hs-game.js'; }
    }
  }
  if (!sdk && root && root.HSTikTokSDK) sdk = root.HSTikTokSDK;

  var started = false;
  var ready = false;             // the SDK initialised (credentials set)
  var loginDone = false;         // the startup login finished, either way
  var giveCb = null;
  var loadCb = null;
  var defaults = { rewards: {}, items: {} };
  var cloudSettled = false;
  var cloudData = null;
  var loadDelivered = false;
  var latest;
  var hasLatest = false;
  var adBusySince = 0;
  var trace = [];

  var has = function (o, k) { return !!o && Object.prototype.hasOwnProperty.call(o, k); };
  var log = function (msg) { try { if (HSGame.debug) console.log('[HSGame] ' + msg); } catch (e) {} };
  var note = function (what) { if (trace.length < 500) trace.push(what); };
  var noteOnce = function (what) { if (trace.indexOf(what) < 0) note(what); };
  var safe = function (fn, fallback) { try { return fn(); } catch (e) { log('error: ' + (e && e.message)); return fallback; } };
  var copy = function (v) { return safe(function () { return JSON.parse(JSON.stringify(v)); }, v); };

  // Device storage: TikTok storage in a mini game, localStorage in a browser
  // or the Android app's WebView. Strings in, strings out, never throws.
  var mem = {};
  function storeGet(key) {
    var t = root && root.tt;
    if (t && typeof t.getStorageSync === 'function') {
      var v = safe(function () { return t.getStorageSync(key); }, '');
      if (v !== '' && v !== null && v !== undefined) return typeof v === 'string' ? v : JSON.stringify(v);
      return has(mem, key) ? mem[key] : null;
    }
    var ls = safe(function () { return root && root.localStorage; }, null);
    var w = ls ? safe(function () { return ls.getItem(key); }, null) : null;
    return w !== null && w !== undefined ? w : (has(mem, key) ? mem[key] : null);
  }
  function storeSet(key, value) {
    mem[key] = value;
    var t = root && root.tt;
    if (t && typeof t.setStorageSync === 'function') { safe(function () { t.setStorageSync(key, value); }); return; }
    var ls = safe(function () { return root && root.localStorage; }, null);
    if (ls) safe(function () { ls.setItem(key, value); });
  }

  // Kit-level events: 'otherDevice', 'given', 'pause', 'resume'.
  var kitListeners = {};
  function kitEmit(name, a, b) {
    var list = (kitListeners[name] || []).slice();
    for (var i = 0; i < list.length; i++) safe(function () { list[i](a, b); });
  }

  // ─── Platform: TikTok Minis, or the HS Android app ───────────────────────
  // The Android app runs these same files in a WebView with a web `tt` shim
  // and injects HSNative (its bridge). It is checked first: the shim has a
  // tt.request too.

  function nativeBridge() {
    var n = root && root.HSNative;
    return n && typeof n === 'object' && n.platform === 'android' ? n : null;
  }

  function platformName() {
    if (nativeBridge()) return 'android';
    var t = root && root.tt;
    if ((t && typeof t.request === 'function') || (root && root.TTMinis && root.TTMinis.game)) return 'minis';
    return 'browser';
  }

  /** The runtime can do it (login, pay…). An SDK too old to say is a TikTok one. */
  function canDo(cap) {
    if (!sdk || !ready) return false;
    var c = safe(function () { return sdk.capabilities; }, null);
    return c && typeof c === 'object' && has(c, cap) ? !!c[cap] : platformName() === 'minis';
  }

  /** A login can work here: the runtime has one, or the SDK runs in test mode (a desktop browser). */
  function loginPossible() {
    return canDo('login') || !!(sdk && ready && safe(function () { return sdk.isTestMode; }, false));
  }

  /** Logged in as an Android device account (dv_…): an account, but still a guest at heart. */
  function onDeviceAccount() {
    return String((sdk && ready && safe(function () { return sdk.openId; }, '')) || '').indexOf('dv_') === 0;
  }

  /** The dashboard switched a feature off: iaa_config "features": { "share": false }. */
  function featureOff(name) {
    var f = remote('features');
    return !!(f && f[name] === false);
  }

  // 'pause' / 'resume': ONE pair however many reasons overlap — an ad that
  // also hides the app pauses once and resumes when both are over.
  var pauseReasons = {};
  function pauseFor(reason) {
    var was = isEmpty(pauseReasons);
    pauseReasons[reason] = true;
    if (was) kitEmit('pause', reason);
  }
  function resumeFrom(reason) {
    if (!has(pauseReasons, reason)) return;
    delete pauseReasons[reason];
    if (isEmpty(pauseReasons)) kitEmit('resume', reason);
  }

  // ─── The reward table: dashboard (iaa_config) over the game's defaults ────

  function remote(section) {
    var cfg = sdk && ready ? safe(function () { return sdk.ads.config; }, null) : null;
    var s = cfg && cfg[section];
    return s && typeof s === 'object' ? s : null;
  }

  /**
   * { items: { hint: 2 }, limit } for a key, or null when it gives nothing.
   * The dashboard wins per key — including `"key": null`, which switches a
   * default reward off. Accepts the old list form [{ type, amount }] too.
   */
  function entry(key) {
    var r = remote('rewards');
    var d = has(defaults.rewards, key) ? defaults.rewards[key] : undefined;
    var raw = has(r, key) ? r[key] : d;
    if (raw === undefined || raw === null || typeof raw !== 'object') return null;
    // The limit is part of what the moment IS: a dashboard entry that only
    // changes the amount keeps the game's own limit — a "once" never becomes
    // "every time" because someone retyped the number.
    var limit = limitOf(raw);
    if (!limit) limit = limitOf(d);
    if (!limit) limit = BUILTIN_LIMIT[key] || 'always';
    return { items: toItems(raw), limit: limit };
  }

  function limitOf(raw) {
    if (!raw || typeof raw !== 'object' || Array.isArray(raw)) return '';
    var l = raw.$limit !== undefined ? raw.$limit : raw.limit;   // `limit` = the 2.x shape
    return l === 'once' || l === 'daily' || l === 'always' ? l : '';
  }

  /**
   * { hint: 2, coins: 50 } from any form: that map itself (keys starting with
   * "$" are settings, not items; true counts as 1), the older list
   * [{ type, amount, value }] products may still carry, or the 2.x shape
   * { rewards: [...], limit }. Zero and negative amounts are dropped.
   */
  function toItems(raw) {
    var items = {};
    if (raw && !Array.isArray(raw) && typeof raw === 'object' && Array.isArray(raw.rewards)) raw = raw.rewards;
    if (Array.isArray(raw)) {
      for (var i = 0; i < raw.length; i++) {
        var x = raw[i];
        var n0 = x ? (Number(x.amount) || (x.value === true ? 1 : 0)) : 0;
        if (x && typeof x.type === 'string' && x.type && n0 > 0) items[x.type] = (items[x.type] || 0) + n0;
      }
    } else if (raw && typeof raw === 'object') {
      for (var k in raw) {
        if (!has(raw, k) || k.charAt(0) === '$') continue;
        var n = raw[k] === true ? 1 : Number(raw[k]);
        if (n > 0) items[k] = n;
      }
    }
    return items;
  }

  function isEmpty(o) { for (var k in o) if (has(o, k)) return false; return true; }

  function catalog() {
    var out = {};
    var d = defaults.items || {};
    var r = remote('items') || {};
    for (var a in d) if (has(d, a)) out[a] = d[a];
    for (var b in r) if (has(r, b)) { if (r[b] === null) delete out[b]; else out[b] = r[b]; }
    return out;
  }

  /**
   * Hands items to the game. True when it took them.
   *
   * With a profile, an item that is a number field of the profile (hint,
   * coins…) is credited to it — no game code. Anything else (a skin unlock…)
   * is "special" and goes to onGive FIRST; the profile is credited only if
   * onGive did not throw, so a retry can never credit the plain part twice.
   */
  function give(items, from) {
    note('give:' + from);
    var special = items;
    var credit = {};
    if (P) {
      special = {};
      for (var id in items) {
        if (!has(items, id)) continue;
        if (typeof P.defs[id] === 'number') credit[id] = items[id];
        else special[id] = items[id];
      }
    }
    if (!isEmpty(special)) {
      if (!giveCb) { log('nothing given for "' + from + '" — ' + Object.keys(special).join(', ') + ' needs onGive (or a number field in the profile)'); return false; }
      var cat = catalog();
      for (var s in special) if (has(special, s) && !isEmpty(cat) && !has(cat, s)) log('item "' + s + '" (from ' + from + ') is not in the items catalog');
      try { giveCb(copy(special), from); }
      catch (e) { log('onGive threw for "' + from + '": ' + (e && e.message) + ' — not recorded'); return false; }
    }
    if (!isEmpty(credit)) {
      var ch = {};
      for (var c in credit) if (has(credit, c)) ch[c] = (Number(P.data[c]) || 0) + (Number(credit[c]) || 0);
      applyChanges(ch, 'reward');
      // On the device at once, not on the 400 ms timer: a claim is recorded
      // right after this, and an app killed in between kept the claim but
      // lost what it paid.
      writeProfileNow();
    }
    // Anything given goes up within a second, not at the 10 s sync tick.
    syncSoon();
    kitEmit('given', copy(items), from);
    return true;
  }

  // ─── Claims: once / daily / always ────────────────────────────────────────
  // In TikTok storage, and inside the cloud save (`_hs`) when the game uses
  // save(), so a reinstall or a new phone does not pay again. `daily` follows
  // the phone's date — never use it for paid value.

  var CLAIMS_KEY = 'hsgame.claims';
  var memClaims = {};

  /** Claims belong to the account that made them (a cloud profile's owner); otherwise to the device. */
  function claimsKey() {
    return CLAIMS_KEY + (P && P.mode === 'cloud' && P.owner ? '.' + P.owner : '');
  }

  function today() {
    var d = new Date();
    var p = function (n) { return (n < 10 ? '0' : '') + n; };
    return d.getFullYear() + '-' + p(d.getMonth() + 1) + '-' + p(d.getDate());
  }

  function loadClaims() {
    var raw = storeGet(claimsKey());
    if (!raw) return memClaims;
    var parsed = safe(function () { return JSON.parse(raw); }, null);
    return parsed && typeof parsed === 'object' ? parsed : memClaims;
  }

  function storeClaims(c) {
    memClaims = c;
    storeSet(claimsKey(), JSON.stringify(c));
    if (cloudSettled && cloudWanted()) cloud.isDirtyForCloud = true;
    markSaveDirty();
  }

  // Claims are merged as a union, also when a newer cloud copy wins over a
  // copy this phone never sent: a "once" claimed there stays claimed. Rolling
  // it back could pay a reinstall twice; the window is the second before the
  // prompt upload, and only when another phone wrote the cloud meanwhile.
  function mergeClaims(other) {
    if (!other || typeof other !== 'object') return;
    var c = loadClaims();
    for (var k in other) {
      if (!has(other, k) || !other[k]) continue;
      var mine = c[k], theirs = other[k];
      if (!mine) { c[k] = theirs; continue; }
      c[k] = { n: Math.max(mine.n || 0, theirs.n || 0), last: (mine.last || '') > (theirs.last || '') ? mine.last : theirs.last };
    }
    storeClaims(c);
  }

  function isClaimed(key, limit) {
    var e = loadClaims()[key];
    if (!e || limit === 'always') return false;
    return limit === 'daily' ? e.last === today() : true;
  }

  function recordClaim(key) {
    var c = loadClaims();
    var e = c[key] || { n: 0, last: '' };
    c[key] = { n: (e.n || 0) + 1, last: today() };
    storeClaims(c);
    syncSoon();
  }

  /** The common path: the key's reward, if any and if its limit allows, given and recorded. */
  function payout(key, from) {
    var e = entry(key);
    if (!e || isEmpty(e.items) || isClaimed(key, e.limit)) return null;
    if (!give(e.items, from || key)) return null;
    recordClaim(key);
    return copy(e.items);
  }

  // ─── Profile (3.1): the game's progress, owned by the kit ─────────────────
  //
  // One object. The game changes it only through set / add / update; every
  // change fires events (for the UI), is written to the device, and — in
  // save:'cloud' — synced. On a new phone, a reinstall or a takeover the cloud
  // copy is merged field by field: 'max' / 'min' for values that only move one
  // way (level, best score), 'latest' (default) for everything else, by
  // server-corrected change time. No 'sum': it doubles on every new phone.
  // Consumables must not use 'max' — it would bring spent items back.

  var PROFILE_KEY = 'hsgame.profile';
  var ORDERS_KEEP = 200;
  var clockOffset = 0;       // server time - device time, ms, learned from cloud syncs (and a login, forward only)
  var P = null;              // the profile state, once HSGame.profile() ran
  var takingOver = false;
  var acceptNextCloud = false;   // a different account logged in: merge its cloud copy too

  function nowMs() { return Date.now() + clockOffset; }
  function same(a, b) { return JSON.stringify(a) === JSON.stringify(b); }

  function profileKey(owner) { return PROFILE_KEY + (owner ? '.' + owner : ''); }

  function readEnvelope(owner) {
    var raw = storeGet(profileKey(owner));
    var env = raw ? safe(function () { return JSON.parse(raw); }, null) : null;
    if (env && typeof env === 'object' && env.data && typeof env.data === 'object') return env;
    // Unreadable (a write cut short) → the backup taken at the last good start.
    var bak = storeGet(profileKey(owner) + '.bak');
    env = bak ? safe(function () { return JSON.parse(bak); }, null) : null;
    if (env && env.data) log('profile: main copy unreadable — restored the backup');
    return env && typeof env === 'object' && env.data && typeof env.data === 'object' ? env : null;
  }

  /** Loads (or creates) the profile of `owner` into P, filling missing fields from the defaults. */
  function loadProfile(owner) {
    var env = readEnvelope(owner);
    P.owner = owner || '';
    P.fresh = !env;
    P.data = copy(P.defs);
    P.t = {};
    P.orders = [];
    if (env) {
      var stored = env.data;
      var from = env.v | 0;
      if (from < P.version && P.migrate) {
        var up = safe(function () { return P.migrate(copy(stored), from); }, null);
        if (up && typeof up === 'object') stored = up;
      }
      for (var k in stored) if (has(stored, k)) P.data[k] = stored[k];
      P.t = env.t && typeof env.t === 'object' ? env.t : {};
      P.orders = Array.isArray(env.o) ? env.o : [];
      // One backup per start, of a copy that just parsed — cheap insurance.
      storeSet(profileKey(owner) + '.bak', JSON.stringify(env));
    }
    if (P.mode === 'cloud' && owner) storeSet(PROFILE_KEY + '.last', owner);
  }

  function writeProfileNow() {
    if (!P) return;
    if (P.timer) { clearTimeout(P.timer); P.timer = null; }
    storeSet(profileKey(P.owner), JSON.stringify({ v: P.version, data: P.data, t: P.t, o: P.orders, owner: P.owner }));
  }

  function scheduleWrite() {
    if (!P || P.timer) return;
    P.timer = setTimeout(function () { P.timer = null; writeProfileNow(); }, 400);
  }

  /** Applies { field: value } and fires events. source: 'game' | 'reward' | 'cloud'. */
  function applyChanges(changes, source, cloudTimes) {
    var fired = {};
    var any = false;
    for (var f in changes) {
      if (!has(changes, f)) continue;
      var before = P.data[f];
      var now = changes[f];
      if (same(before, now)) continue;
      P.data[f] = copy(now);
      P.t[f] = source === 'cloud' ? ((cloudTimes && cloudTimes[f]) || 0) : nowMs();
      fired[f] = [copy(now), copy(before)];
      any = true;
    }
    if (!any) return;
    scheduleWrite();
    if (source !== 'cloud' && cloudSettled && cloudWanted()) cloud.isDirtyForCloud = true;
    fire(fired, source);
  }

  /** Calls the listeners for { field: [now, before] }. Data is already in place. */
  function fire(fired, source) {
    for (var g in fired) {
      if (!has(fired, g)) continue;
      var list = (P.listeners[g] || []).slice();
      for (var i = 0; i < list.length; i++) (function (cb, pair) { safe(function () { cb(pair[0], pair[1]); }); })(list[i], fired[g]);
    }
    var all = (P.listeners['*'] || []).slice();
    for (var j = 0; j < all.length; j++) (function (cb) { safe(function () { cb(copy(fired), source); }); })(all[j]);
  }

  function syncedFields(obj) {
    var out = {};
    for (var k in obj) if (has(obj, k) && !has(P.local, k)) out[k] = obj[k];
    return out;
  }

  /**
   * Merges a cloud copy into the profile, field by field. `stale`: another
   * phone wrote the cloud since this one last saw it — its 'latest' values
   * win, as on a new phone (this phone's unsent changes lose, like 3.0's).
   */
  function mergeIntoProfile(cloudObj, hs, stale, newerCloud) {
    var ct = (hs && hs.t) || {};
    var changes = {};
    var deviceNewer = false;
    for (var f in cloudObj) {
      if (!has(cloudObj, f) || has(P.local, f)) continue;
      var rule = P.rules[f] || 'latest';
      var lv = P.data[f], cv = cloudObj[f], pick;
      var bothNumbers = typeof lv === 'number' && typeof cv === 'number';
      if (rule === 'max' && bothNumbers) {
        // Always the higher — also for a value this device never changed
        // itself (an old save, a migrate()): a default is below any record.
        pick = Math.max(lv, cv);
      } else if (!has(P.t, f)) {
        // Never changed on this device: it still holds the default, which is
        // not a value to compare (a 'min' default of 0 would beat any record).
        pick = cv;
      } else if (rule === 'min' && bothNumbers) {
        pick = Math.min(lv, cv);
      } else if (P.fresh || stale) {
        pick = cv;                      // a new phone / reinstall / a newer cloud: the cloud is the truth
      } else {
        pick = (ct[f] || 0) >= (P.t[f] || 0) ? cv : lv;
      }
      if (!same(pick, cv)) deviceNewer = true;
      if (!same(pick, lv)) changes[f] = pick;
    }
    // Fields this device has that the cloud copy lacks go up with the next sync.
    for (var g in P.data) if (has(P.data, g) && !has(P.local, g) && !has(cloudObj, g)) deviceNewer = true;
    // The cloud's values won: an order this phone credited that the cloud copy
    // does not list is no longer in the profile. It leaves the list, so the
    // backend's next offer credits it again (it was never confirmed: held
    // until an upload holds it) — the rule 3.0 follows too: twice, never lost.
    if (P.fresh || stale || newerCloud) dropOrdersNotIn(hs);
    addOrders(hs);
    applyChanges(changes, 'cloud', ct);
    P.fresh = false;
    writeProfileNow();
    if (deviceNewer) cloud.isDirtyForCloud = true;
  }

  /**
   * The game uses cloud saving: a profile in 'cloud' mode, or the 3.0 save() —
   * also before its first save(): a game with onLoad wants the cloud copy, so
   * a Google purchase recovered at start waits for it (else the copy arriving
   * after the credit would overwrite it).
   */
  function cloudWanted() { return P ? P.mode === 'cloud' : (hasLatest || !!loadCb); }

  // ─── Prompt upload ────────────────────────────────────────────────────────
  // The SDK's own sync runs every 10 s; anything of value (a reward, a claim,
  // a purchase) goes up within about a second instead, so an app killed soon
  // after has it in the cloud. Skipped or failed (the SDK's 3 s cooldown, a
  // sync already running): tried again a few times, then the tick takes over.

  var SYNC_SOON_MS = 1000;
  var syncTimer = null;
  var syncTries = 0;

  /** Upload within a second. A new call restarts the retry count (a new change deserves its tries). */
  var syncTimerRetry = false;

  function syncSoon(retry) {
    if (!retry) syncTries = 0;
    // A new change while only a 3 s retry waits: back to the 1 s timer.
    if (syncTimer && !retry && syncTimerRetry) { clearTimeout(syncTimer); syncTimer = null; }
    if (syncTimer || !sdk || !ready) return;
    syncTimerRetry = !!retry;
    syncTimer = setTimeout(function () {
      syncTimer = null;
      if (!cloudSettled || !cloud.isDirtyForCloud || !safe(function () { return sdk.isAuthenticated; }, false)) return;
      Promise.resolve(safe(function () { return sdk.sync.syncNow(); }, false)).then(function (ok) {
        if (!ok && cloud.isDirtyForCloud && syncTries < 3) { syncTries++; syncSoon(true); }
      }, function () {});
    }, retry ? 3000 : SYNC_SOON_MS);
  }

  // ─── 3.0 save(): this phone's copy, until it is in the cloud ──────────────
  // Without it, an app killed before the sync lost the change: at the next
  // login the older cloud copy went to onLoad. Per account, the kit keeps
  // { data, dirty, ts, o, gp } — the last save(), "not in the cloud yet", the
  // server time of the last login / sync, TikTok orders whose save() came, and
  // Google purchases credited since the last upload. At login the SDK says
  // whether another phone wrote the cloud since this one last saw it (a hash
  // of the copy, not a clock). Unchanged → this phone's copy is kept, handed
  // to onLoad and uploaded. Changed → the cloud copy wins, as before: a stale
  // phone never overwrites newer progress from another phone (its unsent
  // change is lost — the strict choice). Offline, the copy belongs to the
  // account that played here last (like profile.last), so offline progress
  // is kept too.

  var SAVE_KEY = 'hsgame.save';
  var decided = false;      // this session knows whose copy it is, and chose between it and the cloud's
  var saveOwner = '';       // that account: the logged-in one, or offline the last one
  var baseTs = 0;           // server time of the last login / sync (for the record; the choice uses the SDK's hash)
  var orders0 = [];         // 3.0: TikTok order ids in the save (travel as _hs.orders)
  var ordersNew = [];       // 3.0: credited, but the game has not called save() since
  var gpNew = [];           // 3.0: Google purchases credited since the last upload
  var cloudOrders = {};     // order ids the cloud copy holds (read at login, or just uploaded)

  function readSave() {
    var raw = saveOwner ? storeGet(SAVE_KEY + '.' + saveOwner) : null;
    var env = raw ? safe(function () { return JSON.parse(raw); }, null) : null;
    return env && typeof env === 'object' ? env : null;
  }

  function writeSave(dirty) {
    if (P || !decided || !saveOwner) return;
    // Orders credited but in no save() yet are NOT stored: after a restart the
    // game gets the last save(), which lacks them, so they are credited again
    // (twice at worst, never lost). RULE: a 3.0 game calls save() in onGive.
    storeSet(SAVE_KEY + '.' + saveOwner, JSON.stringify({ data: hasLatest ? latest : null, dirty: !!dirty, ts: baseTs, o: orders0, gp: gpNew }));
  }

  /**
   * A change that is not in the cloud yet. Only once the session knows whose
   * copy it is (before that, a save() is the fresh-install state, never kept).
   */
  function markSaveDirty() { if (!P && decided) writeSave(true); }

  // ordersNew counts here only in memory: an order offered twice in ONE session
  // (a buy's poll and a resume's recovery) is credited once.
  function knownOrder0(id) { return orders0.indexOf(String(id)) >= 0 || ordersNew.indexOf(String(id)) >= 0; }

  /**
   * This phone's copy is the session's save: its data (also over a save()
   * made at boot — that may be defaults), its orders, its Google credits —
   * and it goes to onLoad, so a game that keeps no storage of its own gets
   * it back. `extraOrders`: order ids the cloud copy also lists.
   */
  function useSaved(env, extraOrders) {
    if (env.data && typeof env.data === 'object') { latest = copy(env.data); hasLatest = true; cloudData = copy(env.data); }
    var o = (Array.isArray(env.o) ? env.o : []).concat(extraOrders || []);
    orders0 = [];
    for (var i = 0; i < o.length; i++) if (orders0.indexOf(String(o[i])) < 0) orders0.push(String(o[i]));
    ordersNew = [];
    gpNew = Array.isArray(env.gp) ? env.gp.slice() : [];
  }

  /** Logged in, no (readable) cloud copy: this phone's own copy, if any, is the account's. */
  function decideWithoutCloud() {
    var env = readSave();
    decided = true;
    if (env && env.data) { useSaved(env); loadDelivered = false; deliverLoad(); }
    if (env && env.dirty) { cloudDirty = true; syncSoon(); }
  }

  /** The startup login failed: the session's copy is the last account's own (H3). */
  function decideOffline() {
    if (P || decided) return;
    saveOwner = storeGet(SAVE_KEY + '.last') || '';
    // Nobody ever logged in here: a fresh install. Its offline play is the
    // fresh-install state the kit never sets against an account's cloud copy;
    // the game's onLoad merges that copy with its own storage at the first
    // login (as before 3.2.3) — the kit does not know which account it is.
    if (!saveOwner) return;
    var env = readSave();
    decided = true;
    if (env && env.data) { useSaved(env); deliverLoad(); }
  }

  /**
   * The cloud copy won over a copy this phone never sent: what was credited
   * into that copy is gone with it. TikTok orders: never confirmed (held by
   * the SDK until an upload holds them), so the backend offers them again and
   * they are credited into the cloud copy. Google: the keys leave the device
   * list, so a permanent item Google still returns is credited again; a
   * consumable was already finished at Google and is lost — only when another
   * phone wrote the cloud in the second before the upload. A game whose
   * onLoad keeps its own value over the cloud's (a "keep the higher" merge)
   * then has such an order twice: the SDK's rule, twice rather than lost.
   */
  function dropUnsent(env, hs) {
    var inCloud = hs && Array.isArray(hs.gp) ? hs.gp : [];
    var drop = (Array.isArray(env.gp) ? env.gp : []).filter(function (k) { return inCloud.indexOf(k) < 0; });
    if (drop.length) storeSet(GP_CREDITED, JSON.stringify(readList(GP_CREDITED).filter(function (k) { return drop.indexOf(k) < 0; })));
  }

  // ─── Cloud provider (the SDK's sync) ──────────────────────────────────────

  var cloudDirty = false;
  var conflict = null;       // { data, hs, info } while the player chooses which progress to keep

  var cloud = {
    // Nothing goes up while the player is choosing: the SDK only uploads when
    // this reads true, and the change waits until the choice is made. A 3.0
    // game that never saved has nothing to upload ({} would wipe the cloud).
    get isDirtyForCloud() { return cloudDirty && !conflict && (!!P || hasLatest); },
    set isDirtyForCloud(v) { cloudDirty = !!v; },
    serializeForCloud: function () {
      var out = {};
      if (P) {
        if (P.mode !== 'cloud') return {};
        out = syncedFields(P.data);
        out._hs = { claims: loadClaims(), t: syncedFields(P.t), orders: trimOrders(P.orders), v: P.version };
        return out;
      }
      if (!hasLatest) return {};
      for (var k in latest) if (has(latest, k)) out[k] = latest[k];
      var c = loadClaims();
      // 3.0 save(): Google purchases already credited travel too — a reinstall
      // must not credit a permanent one again on top of the restored save.
      // TikTok orders too: a kept copy says which orders are already in it.
      var gp = readList(GP_CREDITED);
      if (!isEmpty(c) || gp.length || orders0.length) {
        out._hs = {};
        if (!isEmpty(c)) out._hs.claims = c;
        if (gp.length) out._hs.gp = gp;
        if (orders0.length) out._hs.orders = orders0.slice();
      }
      // No side effects here: the SDK may read a copy it does not send now
      // (a hide while a sync runs). What was sent comes back in onCloudSyncSuccess.
      return out;
    },
    /** SDK 1.1.2 passes `uploaded`: the copy that reached the cloud, maybe older than this phone's state. */
    onCloudSyncSuccess: function (ts, uploaded) {
      if (ts > 0) baseTs = ts;
      if (!uploaded || typeof uploaded !== 'object') return;
      var hs = uploaded._hs;
      cloudOrders = {};
      var o = hs && Array.isArray(hs.orders) ? hs.orders : [];
      for (var i = 0; i < o.length; i++) cloudOrders[String(o[i])] = true;
      // The cloud now holds exactly this phone's state: nothing unsent is left.
      if (!P && same(uploaded, cloud.serializeForCloud())) { gpNew = []; writeSave(false); }
    },
    /**
     * SDK 1.1.2: true while the cloud copy does not hold this paid order. The
     * SDK confirms it to the backend once an uploaded copy does. Any game that
     * saves to the cloud holds — also a 3.0 game whose first save() comes
     * after the credit (onLoad set). A game that saves nowhere (no onLoad, no
     * save(), profile 'local') confirms at once, as before.
     */
    holdOrderConfirmation: function (orderId) {
      return cloudWanted() && !has(cloudOrders, String(orderId));
    },
    onCloudDataReceived: function (json, ts, info) {
      // Only the first login of a session counts — unless the player chose
      // "play here" (takeOver), or a different account just logged in on this
      // phone: both pull and merge again.
      if (cloudSettled && !takingOver && !acceptNextCloud) { log('ignoring cloud data from a later login'); return; }
      acceptNextCloud = false;
      if (ts > 0) baseTs = ts;
      var data = safe(function () { return JSON.parse(json); }, null);
      if (!data || typeof data !== 'object') return;
      var env = P ? null : readSave();     // 3.0: as it was before this login touched anything
      var hs = data._hs || null;
      cloudOrders = {};                    // what THIS cloud copy holds — nothing from earlier copies
      if (hs) {
        mergeClaims(hs.claims);
        if (!P && Array.isArray(hs.gp)) mergeCredited(hs.gp);
        // This phone's own queued save (info.pending) is not in the cloud yet.
        if (Array.isArray(hs.orders) && !(info && info.pending)) {
          for (var i = 0; i < hs.orders.length; i++) cloudOrders[String(hs.orders[i])] = true;
        }
        delete data._hs;
      }

      if (P) {
        // A guest who made progress, joining an account that has its own:
        // which one wins is the player's call, never a silent overwrite.
        if (P.mode === 'cloud' && P.joining && guestProgressed() && accountDiffers(data)) {
          P.joining = false;
          // Paid orders wait for the choice (onOrder); it merges the account's
          // delivered ids first, then fetches them again — credited once.
          askWhichProgress(data, hs);
          return;
        }
        P.joining = false;
        // Always, even when the copy holds only orders / claims: the delivered
        // order ids must come down, or another phone's order is credited twice.
        // Another phone wrote the cloud since this one last saw it: its values
        // win (as on a new phone) — a stale phone's clock never decides. Not
        // for "Play here" (takeOver): its promise is to merge this phone's own
        // progress in, by change time, as before.
        // Either way, order ids that newer copy lacks leave the profile (the
        // backend offers them again): a field it won may have dropped them.
        var newer = !!(info && info.known && !info.unchanged && !info.pending);
        if (P.mode === 'cloud') mergeIntoProfile(data, hs, newer && !takingOver, newer);
        return;
      }
      if (!info) {
        // An SDK before 1.1.2 cannot say whether the cloud changed: as before —
        // and that choice is final, so this phone's stored copy is never
        // handed over or uploaded after it (decideWithoutCloud).
        decided = true;
        if (!isEmpty(data)) { latest = copy(data); hasLatest = true; cloudData = data; if (takingOver) loadDelivered = false; deliverLoad(); }
        return;
      }
      // 3.0 save(): a copy this phone saved but never sent, and nobody wrote
      // the cloud since → it is newer than the cloud copy: kept, handed to
      // onLoad, and uploaded within a second. A cloud copy with no game data
      // at all has nothing to win with either.
      var keep = !!(env && env.dirty && (info.unchanged || isEmpty(data)));
      var cloudOrders0 = hs && Array.isArray(hs.orders) ? hs.orders : [];
      decided = true;
      if (keep) {
        // onLoad gets this phone's copy once a session: a session that started
        // offline already handed it over, and its saves since ARE this copy.
        useSaved(env, cloudOrders0);
        note('cloud:kept this phone');
        log('cloud copy older than this phone\'s unsent save — keeping this phone\'s');
        writeSave(true);
        cloudDirty = true;
        syncSoon();
      } else {
        if (env && env.dirty) dropUnsent(env, hs);
        loadDelivered = false;          // a copy the game has not seen: it merges it
        orders0 = cloudOrders0.map(String);
        ordersNew = [];
        gpNew = [];
        cloudData = null;
        if (!isEmpty(data)) {
          // The pre-login save is the fresh-install state — drop it, never
          // upload it. Until the game saves its merge, the cloud copy IS the
          // save, so claims recorded meanwhile still travel with it.
          latest = copy(data); hasLatest = true;
          cloudData = data;
        }
        writeSave(false);
      }
      deliverLoad();                  // the game's merge, saved, is marked unsent
      // settleCloud() runs on loginSuccess, after this, for every login path.
    }
  };

  /** 3.1: drops the order ids (and Google keys) the cloud copy does not list. */
  function dropOrdersNotIn(hs) {
    var inCloud = {};
    var list = hs && Array.isArray(hs.orders) ? hs.orders : [];
    for (var i = 0; i < list.length; i++) inCloud[String(list[i])] = true;
    var gone = P.orders.filter(function (k) { return !has(inCloud, String(k)); });
    if (!gone.length) return;
    P.orders = P.orders.filter(function (k) { return has(inCloud, String(k)); });
    // A permanent Google item Google still returns is then credited again; a
    // consumable was finished at Google already (see dropUnsent).
    storeSet(GP_CREDITED, JSON.stringify(readList(GP_CREDITED).filter(function (k) { return gone.indexOf(k) < 0; })));
  }

  /** Order ids a cloud copy lists, into the profile's (3.1). */
  function addOrders(hs) {
    if (!hs || !Array.isArray(hs.orders)) return;
    for (var i = 0; i < hs.orders.length; i++) if (!orderKnown(hs.orders[i])) P.orders.push(String(hs.orders[i]));
    P.orders = trimOrders(P.orders);
  }

  // ─── Guest progress meets an account's own progress ───────────────────────

  /** The field that sums up progress for the "which one?" question: opts.summary, the first 'max' field, or level. */
  function summaryField() {
    if (P.summary && has(P.defs, P.summary)) return P.summary;
    for (var f in P.rules) if (has(P.rules, f) && P.rules[f] === 'max' && has(P.defs, f)) return f;
    return has(P.defs, 'level') ? 'level' : '';
  }

  /**
   * The guest really played: the summary field moved off its default (else any
   * synced field changed). A guest who bought something always counts — its
   * items must never be overwritten without asking.
   */
  function guestProgressed() {
    if (P.orders.length) return true;
    var f = summaryField();
    if (f) return has(P.t, f) && !same(P.data[f], P.defs[f]);
    for (var k in P.t) if (has(P.t, k) && !has(P.local, k)) return true;
    return false;
  }

  /**
   * The account's copy says something else than this phone (any field, once the guest bought something).
   * Known and kept on purpose: a guest who only earned small things (hints
   * from an ad) at the account's own level joins it without a question, and
   * the account's values win. Asking on every small difference would put the
   * popup in front of almost every first sign-in; paid items always ask.
   */
  function accountDiffers(data) {
    var f = summaryField();
    if (f && !P.orders.length) return has(data, f) && !same(data[f], P.data[f]);
    for (var k in data) if (has(data, k) && !has(P.local, k) && !same(data[k], P.data[k])) return true;
    return false;
  }

  function askWhichProgress(data, hs) {
    var f = summaryField();
    var info = { field: f, device: f ? copy(P.data[f]) : null, account: f ? copy(data[f]) : null };
    conflict = { data: data, hs: hs, info: info };
    note('accountConflict');
    var answered = false;
    var choose = function (which) {
      if (answered) return;
      answered = true;
      resolveConflict(which === 'device' ? 'device' : 'account');
    };
    // The game's own screen, if it has one…
    if ((kitListeners.accountConflict || []).length) { kitEmit('accountConflict', copy(info), choose); return; }
    // …else the system's confirm popup (TikTok, and the web shim in the app).
    var t = root && root.tt;
    if (t && typeof t.showModal === 'function') {
      var label = f ? f.replace(/_/g, ' ') : 'progress';
      safe(function () {
        t.showModal({
          title: 'Choose your progress',
          content: 'This account already has saved progress (' + label + ' ' + info.account + '). ' +
                   'This phone has ' + label + ' ' + info.device + '. Which one do you keep?',
          confirmText: 'Account', cancelText: 'This phone', showCancel: true,
          success: function (r) { choose(r && r.confirm ? 'account' : 'device'); },
          fail: function () { choose('account'); }
        });
      });
      return;
    }
    choose('account');   // nothing to ask with: the account's progress, as before
  }

  function resolveConflict(which) {
    var c = conflict;
    if (!c) return;
    // The side not kept stays on this phone — a wrong tap can be undone by support.
    storeSet(profileKey(P.owner) + '.conflict', JSON.stringify({ kept: which, device: P.data, account: c.data, at: Date.now() }));
    conflict = null;
    note('accountConflict:' + which);
    if (which === 'account') {
      P.fresh = true;
      mergeIntoProfile(c.data, c.hs);
    } else {
      // This phone's progress becomes the account's. Delivered orders still
      // come down, or another phone's purchase would be credited twice.
      addOrders(c.hs);
      for (var f in P.data) if (has(P.data, f) && !has(P.local, f)) P.t[f] = nowMs();
      P.fresh = false;
      writeProfileNow();
      cloud.isDirtyForCloud = true;
    }
    syncSoon();
    kitEmit('accountChosen', which);
    // Paid orders were turned away while the player chose (the choice could
    // have overwritten them): fetch and credit them now, into the kept progress.
    if (sdk && ready) safe(function () { sdk.iap.checkPendingRewards(); });
    if (billing()) recoverGoogle();
  }

  function settleCloud() {
    if (cloudSettled) return;
    cloudSettled = true;
    if (cloudWanted()) cloud.isDirtyForCloud = true;
  }

  function deliverLoad() {
    if (loadDelivered || !cloudData || !loadCb) return;
    loadDelivered = true;
    note('onLoad');
    var data = cloudData;
    safe(function () { loadCb(data); });
  }

  /**
   * On every login (loginSuccess fires just before the SDK hands over the
   * cloud copy): a different TikTok / Google account on this phone gets its
   * own profile — never the previous account's progress.
   */
  /** Returns true when the profile now belongs to a different account than before. */
  function onAccount(openId) {
    if (!P || P.mode !== 'cloud' || !openId) return false;
    if (P.owner === openId) return false;
    var guestClaims = (!P.owner || P.owner.indexOf('dv_') === 0) ? storeGet(claimsKey()) : null;

    // A device account (dv_…, the Android app without Google sign-in) is a
    // guest too: its progress joins a Google account signed in to later — and
    // a guest's progress joins the device account itself on its first login.
    var guestOwner = !P.owner || P.owner.indexOf('dv_') === 0;
    if (guestOwner && !storeGet(profileKey(openId))) {
      // Played before the first login, and this phone has nothing for this
      // account: the progress joins the account — but like a new phone, so
      // its cloud copy wins (except 'max' / 'min' fields) instead of being
      // overwritten by fresh device times.
      P.owner = openId;
      P.fresh = true;
      P.joining = true;                    // its cloud copy, if any, may ask the player first
      writeProfileNow();
      storeSet(PROFILE_KEY + '.last', openId);
      // The guest's claims join the account with its progress.
      if (guestClaims && !storeGet(claimsKey())) storeSet(claimsKey(), guestClaims);
      memClaims = {};
      acceptNextCloud = true;
      return true;
    }

    // A different account (or one with its own copy on this phone): keep the
    // previous copy where it was, load this account's, and let its cloud copy
    // merge even though this session already logged in once.
    writeProfileNow();
    var before = copy(P.data);
    loadProfile(openId);
    var fired = {};
    var keys = {};
    var k;
    for (k in before) if (has(before, k)) keys[k] = true;
    for (k in P.data) if (has(P.data, k)) keys[k] = true;
    for (k in keys) if (!same(P.data[k], before[k])) fired[k] = [copy(P.data[k]), copy(before[k])];
    memClaims = {};                       // the claims are this account's from here on
    acceptNextCloud = true;
    fire(fired, 'account');
    return true;
  }

  // ─── Purchases: one route, the same onGive ────────────────────────────────

  var lastBuyGiven = null;   // whether the order of the buy() in progress reached the game

  /** Order ids compare as text: one path may say 1042, another "1042". */
  function orderKnown(id) {
    var s = String(id);
    for (var i = 0; i < P.orders.length; i++) if (String(P.orders[i]) === s) return true;
    return false;
  }

  function onOrder(o) {
    note('order:' + o.product_id);
    var items = toItems(o.rewards);
    var ok = false;
    try {
      // Already credited — on this phone or another one whose profile came
      // down with the cloud copy — but its confirmation never reached the
      // backend, so it is offered again. Taking it without crediting lets the
      // SDK confirm it; crediting would grant it twice.
      var oid = o.order_id;
      var hasId = oid !== undefined && oid !== null && oid !== '' && oid !== 0;
      // The player is choosing between this phone's progress and the account's:
      // a credit now could be overwritten by the choice. Kept (not confirmed);
      // fetched again once the choice is made.
      if (conflict) throw new Error('order ' + o.order_id + ' waits for the progress choice — order kept');
      if (hasId && (P ? orderKnown(oid) : knownOrder0(oid))) {
        log('order #' + o.order_id + ' was already credited — confirming only');
        ok = true;
        // The SDK confirms it once an uploaded copy holds it: make sure one goes up.
        if (!has(cloudOrders, String(oid)) && cloudWanted()) { cloudDirty = true; syncSoon(); }
        return;
      }
      // Throwing is the "not taken" signal: the SDK does not confirm the order,
      // so the next login delivers it again. A paid order is stricter than a
      // claim: nothing to give, or an item this build does not know, is kept
      // rather than "given" to a game that would silently ignore it.
      if (isEmpty(items)) throw new Error('product ' + o.product_id + ' gives no item — order kept');
      var cat = catalog();
      for (var id in items) {
        if (!has(items, id)) continue;
        var known = (P && typeof P.defs[id] === 'number') || isEmpty(cat) || has(cat, id);
        if (!known) throw new Error('item "' + id + '" is not in the catalog — order kept');
      }
      // 3.0: the order is in the save from the game's NEXT save() on (in onGive,
      // or later) — only then does it travel with it, and only an uploaded
      // copy that lists it lets the SDK confirm it.
      var sid = String(oid);
      if (!P && hasId) ordersNew.push(sid);
      if (!give(items, 'product:' + o.product_id)) {
        ordersNew = ordersNew.filter(function (x) { return x !== sid; });
        throw new Error('product ' + o.product_id + ' was not taken — order kept');
      }
      if (P && hasId) {
        P.orders.push(sid);
        P.orders = trimOrders(P.orders);
        writeProfileNow();                       // before the SDK confirms it
      }
      // Also during the login (before the cloud settles): the SDK then knows
      // the game holds newer changes than a save queued on hide, and does not
      // resend that older copy first (nor start its cooldown).
      if (cloudWanted()) cloud.isDirtyForCloud = true;
      ok = true;
    } finally {
      if (!o.recovered) lastBuyGiven = ok;
    }
  }

  // ─── Google Play purchases (the HS Android app, client-only billing v1) ────
  // The app's billing plugin returns only purchases whose Google signature it
  // checked with the game's licensing key. The kit credits each one ONCE (its
  // order id is remembered on the device and in the cloud profile), and only
  // then tells Google it is finished — a crash in between leaves it owned, and
  // the next start credits it. Each purchase is also reported to the server.

  var GP_CREDITED = 'hsgame.gp.credited';   // device list of credited purchase keys
  var GP_REPORTS = 'hsgame.gp.reports';     // purchases still to report to the server
  var googleProducts = {};                  // google id → the HS product (raw, with rewards)

  function billing() {
    var nb = nativeBridge();
    return nb && nb.billing && typeof nb.billing.buy === 'function' ? nb.billing : null;
  }

  /** A purchase's product, order id and token — from the app's object, else Google's own JSON. */
  function gpInfo(p) {
    var j = (p && typeof p.json === 'string' && safe(function () { return JSON.parse(p.json); }, null)) || {};
    var text = function () {
      for (var i = 0; i < arguments.length; i++) if (typeof arguments[i] === 'string' && arguments[i]) return arguments[i];
      return '';
    };
    return {
      product: text(p && p.productId, j.productId, Array.isArray(j.productIds) ? j.productIds[0] : ''),
      order: text(p && p.orderId, j.orderId),
      token: text(p && p.token, p && p.purchaseToken, j.purchaseToken)
    };
  }

  /** A permanent item (a skin): Google keeps it owned and returns it at every start. */
  function isPermanent(product) { return !!product && product.consumable === false; }

  /**
   * The key a purchase is remembered by; '' when it has neither order id nor
   * token (such a purchase is never credited — two of them would look alike).
   * Permanent ones get their own prefix: they never age out of the lists.
   */
  function purchaseKey(p, product) {
    var g = gpInfo(p);
    var id = g.order || g.token;
    return id ? (isPermanent(product) ? 'gpo:' : 'gp:') + id : '';
  }

  /** The newest ORDERS_KEEP keys — plus every permanent purchase, which must stay known for good. */
  function trimOrders(list) {
    if (list.length <= ORDERS_KEEP) return list;
    var older = list.slice(0, -ORDERS_KEEP).filter(function (k) { return String(k).indexOf('gpo:') === 0; });
    return older.concat(list.slice(-ORDERS_KEEP));
  }

  function readList(key) {
    var raw = storeGet(key);
    var v = raw ? safe(function () { return JSON.parse(raw); }, null) : null;
    return Array.isArray(v) ? v : [];
  }

  function googleCredited(key) { return (P && orderKnown(key)) || readList(GP_CREDITED).indexOf(key) >= 0; }

  /** Purchases credited on another install (3.0 save(): they come with the cloud copy). */
  function mergeCredited(keys) {
    var list = readList(GP_CREDITED);
    keys.forEach(function (k) { if (typeof k === 'string' && list.indexOf(k) < 0) list.push(k); });
    storeSet(GP_CREDITED, JSON.stringify(trimOrders(list)));
  }

  /** Credit a checked Google purchase once. True when its items are in (now or before). */
  function creditGoogle(p, product) {
    var key = purchaseKey(p, product);
    if (!key) { log('Google purchase without an order id or token — not credited'); return false; }
    if (googleCredited(key)) return true;
    // The player is choosing which progress to keep: left unfinished at
    // Google, credited once the choice is made (resolveConflict recovers it).
    if (conflict) { log('Google purchase waits for the progress choice — kept'); return false; }
    var items = toItems(product && product.rewards);
    // As strict as a TikTok order: nothing to give, or an item this build does
    // not know, is NOT credited — the purchase stays owned and comes back.
    if (isEmpty(items)) { log('Google purchase of ' + gpInfo(p).product + ' gives no item — kept'); return false; }
    var cat = catalog();
    for (var id in items) {
      if (!has(items, id)) continue;
      if (!((P && typeof P.defs[id] === 'number') || isEmpty(cat) || has(cat, id))) { log('item "' + id + '" unknown — Google purchase kept'); return false; }
    }
    if (!give(items, 'product:' + (product.product_id || product.id))) return false;
    var list = readList(GP_CREDITED);
    list.push(key);
    storeSet(GP_CREDITED, JSON.stringify(trimOrders(list)));
    if (P) {
      P.orders.push(key);
      P.orders = trimOrders(P.orders);
      writeProfileNow();
    } else {
      // 3.0: kept with the save that holds it (see dropUnsent).
      gpNew.push(key);
      markSaveDirty();
    }
    if (cloudSettled && cloudWanted()) cloud.isDirtyForCloud = true;
    var q = readList(GP_REPORTS);
    q.push({ json: p.json, signature: p.signature, tries: 0 });
    storeSet(GP_REPORTS, JSON.stringify(q.slice(-ORDERS_KEEP)));
    flushGoogleReports();
    return true;
  }

  /** Tell Google the purchase is done: consumed (can be bought again) or acknowledged (owned for good). */
  function finishGoogle(p, product) {
    var b = billing();
    var token = gpInfo(p).token;
    if (!b || typeof b.finish !== 'function' || !token) return;
    var consumable = !isPermanent(product);
    safe(function () { Promise.resolve(b.finish({ token: token, consumable: consumable })).then(null, function (e) { log('finish failed: ' + (e && e.message)); }); });
  }

  var reporting = false;
  var REPORT_TRIES = 10;     // a report the server keeps refusing is dropped after this many
  /** Send queued purchases to the server (needs a session; the rest wait for the next login). */
  function flushGoogleReports() {
    if (reporting || !sdk || !ready || !sdk.isAuthenticated) return;
    var q = readList(GP_REPORTS);
    if (!q.length) return;
    reporting = true;
    var tried = {};
    // Change one queued report (by its json); fn returns null to drop it.
    var update = function (json, fn) {
      var now = [];
      readList(GP_REPORTS).forEach(function (x) {
        if (!x || x.json !== json) { now.push(x); return; }
        var y = fn(x);
        if (y) now.push(y);
      });
      storeSet(GP_REPORTS, JSON.stringify(now));
    };
    var failed = function (json) {
      update(json, function (x) {
        x.tries = (x.tries || 0) + 1;
        if (x.tries < REPORT_TRIES) return x;
        log('a purchase report was refused ' + x.tries + ' times — dropped');
        return null;
      });
    };
    var next = function (i) {
      if (i >= q.length) {
        // Purchases queued while this ran go too.
        var more = readList(GP_REPORTS).filter(function (x) { return x && !has(tried, x.json); });
        if (!more.length) { reporting = false; return; }
        q = q.concat(more);
      }
      var entry = q[i];
      if (!entry || typeof entry.json !== 'string') { update(entry && entry.json, function () { return null; }); next(i + 1); return; }
      tried[entry.json] = true;
      Promise.resolve(safe(function () { return sdk.iap.reportStorePurchase(entry.json, entry.signature); }, null)).then(function (r) {
        if (r && r.success) update(entry.json, function () { return null; });
        else failed(entry.json);
        next(i + 1);
      }, function () { failed(entry.json); next(i + 1); });
    };
    next(0);
  }

  function findGoogleProduct(productId) {
    var want = String(productId);
    for (var gid in googleProducts) {
      if (!has(googleProducts, gid)) continue;
      var p = googleProducts[gid];
      if (String(p.product_id) === want || String(p.id) === want || gid === want) return p;
    }
    return null;
  }

  var buyingGoogle = null;   // the open purchase (one at a time: Google shows one sheet)

  /** HSGame.buy() in the Android app: Google Play's sheet → credit once → finish. */
  function buyGoogle(productId) {
    if (buyingGoogle) return Promise.resolve({ ok: false, error: 'A purchase is already open', delivered: false });
    var b = billing();
    var mine = {};
    buyingGoogle = mine;
    var release = function () { if (buyingGoogle === mine) buyingGoogle = null; };
    var product = findGoogleProduct(productId);
    var found = product ? Promise.resolve(product) : loadGoogleProducts().then(function () { return findGoogleProduct(productId); });
    return found.then(function (prod) {
      if (!prod) return { ok: false, error: 'Unknown product', delivered: false };
      pauseFor('buy');
      // A sheet that never answers must not freeze the game, nor block buying for good.
      var cap = setTimeout(function () { resumeFrom('buy'); release(); }, BUY_PAUSE_MAX_MS);
      var buying;
      try { buying = Promise.resolve(b.buy(prod.google_id)); } catch (e) { buying = Promise.reject(e); }
      return buying.then(function (r) {
        clearTimeout(cap);
        resumeFrom('buy');
        if (!r || !r.ok || !r.purchase) {
          var error = (r && r.cancelled) ? 'Cancelled' : ((r && r.error) || 'Purchase failed');
          // Google still holds an earlier one (its finish failed): credit and finish it now.
          if (/already.?owned/i.test(error)) recoverGoogle();
          return { ok: false, error: error, delivered: false };
        }
        // What Google sold decides what is given — not the button that was tapped.
        var sold = gpInfo(r.purchase).product;
        var real = sold === prod.google_id ? prod : (has(googleProducts, sold) ? googleProducts[sold] : null);
        if (!real) {
          log('Google sold "' + sold + '", not "' + prod.google_id + '" — not credited');
          return { ok: true, error: '', delivered: false };
        }
        var given = creditGoogle(r.purchase, real);
        if (given) finishGoogle(r.purchase, real);
        // Paid but not given (unknown item, onGive threw): left unfinished at
        // Google, credited at the next start — tell the player it is on its way.
        return { ok: true, error: '', delivered: given };
      }, function (e) {
        clearTimeout(cap);
        resumeFrom('buy');
        return { ok: false, error: String(e && e.message || e), delivered: false };
      });
    }).then(function (res) { release(); return res; }, function (e) {
      release();
      return { ok: false, error: String(e && e.message || e), delivered: false };
    });
  }

  var googleLoaded = false;    // googleProducts came from the server at least once
  var recoverWanted = false;   // a recovery is waiting: for the products, or for the cloud copy

  /** Purchases Google still holds — unfinished (a crash before finish) or permanent: credit what is new. */
  function recoverGoogle() {
    var b = billing();
    if (!b || typeof b.owned !== 'function') return Promise.resolve();
    // The cloud copy, not read yet, may already hold them (a reinstall):
    // crediting first would be overwritten by it. The login calls back here.
    if (cloudWanted() && loginPossible() && !cloudSettled) { recoverWanted = true; return Promise.resolve(); }
    var products = googleLoaded ? Promise.resolve() : loadGoogleProducts();
    return products.then(function () {
      // Offline: what each purchase gives is unknown — again once the shop loads.
      if (!googleLoaded) { recoverWanted = true; return; }
      recoverWanted = false;
      return Promise.resolve(safe(function () { return b.owned(); }, [])).then(function (list) {
        (list || []).forEach(function (p) {
          var pid = gpInfo(p).product;
          var product = has(googleProducts, pid) ? googleProducts[pid] : null;
          if (!product) { log('owned Google purchase of unknown product ' + pid + ' — left for a build that knows it'); return; }
          if (creditGoogle(p, product)) finishGoogle(p, product);
        });
      }, function () {});
    });
  }

  /** HS dashboard products that are on sale in Google Play (a `google_id` + Google's price). */
  function loadGoogleProducts() {
    var b = billing();
    if (!b || !sdk || !ready) return Promise.resolve([]);
    return Promise.resolve(safe(function () { return sdk.iap.getShopItems(); }, null)).then(function (r) {
      // Offline: keep what an earlier load found.
      if (!r || !r.success) return [];
      var mine = (r.data || []).filter(function (p) { return p && typeof p.google_id === 'string' && p.google_id; });
      googleProducts = {};
      mine.forEach(function (p) { googleProducts[p.google_id] = p; });
      googleLoaded = true;
      if (!mine.length || typeof b.products !== 'function') return [];
      return Promise.resolve(b.products(mine.map(function (p) { return p.google_id; }))).then(function (prices) {
        var byId = {};
        (prices || []).forEach(function (g) { if (g && g.id) byId[g.id] = g; });
        return mine.filter(function (p) { return has(byId, p.google_id); }).map(function (p) {
          var out = {};
          for (var k in p) if (has(p, k) && k !== 'rewards') out[k] = p[k];
          out.items = toItems(p.rewards);
          out.price = byId[p.google_id].price;          // Google's localized text, e.g. "₫25,000"
          out.currency = byId[p.google_id].currency;
          return out;
        });
      });
    }, function () { return []; });
  }

  // ─── TikTok APIs the backend is not involved in (missions, share) ─────────

  function tiktok(name) {
    var g = root && root.TTMinis && root.TTMinis.game;
    if (g && typeof g[name] === 'function') {
      var can = typeof g.canIUse !== 'function' || safe(function () { return g.canIUse(name); }, false);
      if (can) return g;
    }
    var t = root && root.tt;
    return t && typeof t[name] === 'function' ? t : null;
  }

  /**
   * Calls a callback-style TikTok API. Resolves { ok, res, err }; never
   * rejects, and never hangs: a host that answers nothing (backgrounded
   * mid-call) resolves 'timeout' after `ms`, and a late answer is dropped.
   */
  function callTikTok(name, args, ms) {
    return new Promise(function (resolve) {
      var settled = false;
      var done = function (r) { if (settled) return; settled = true; clearTimeout(timer); resolve(r); };
      var timer = setTimeout(function () { done({ ok: false, err: 'timeout' }); }, ms || 15000);
      var host = tiktok(name);
      if (!host) return done({ ok: false, err: 'unsupported' });
      var o = {};
      for (var k in (args || {})) o[k] = args[k];
      o.success = function (res) { done({ ok: true, res: res }); };
      o.fail = function (e) { done({ ok: false, err: (e && (e.errMsg || e.message)) || 'failed' }); };
      try { host[name](o); } catch (e) { done({ ok: false, err: String(e && e.message || e) }); }
    });
  }

  /**
   * The Android app's share sheet, in callTikTok's { ok, err } shape. `ok` =
   * the player picked an app to share to (Android cannot confirm the post
   * itself) — so the share reward stays once a day.
   */
  function shareNative(opts) {
    return new Promise(function (resolve) {
      var settled = false;
      var done = function (r) { if (settled) return; settled = true; clearTimeout(timer); resolve(r); };
      var timer = setTimeout(function () { done({ ok: false, err: 'timeout' }); }, 120000);
      var nb = nativeBridge();
      if (!nb || typeof nb.share !== 'function') return done({ ok: false, err: 'unsupported' });
      var req = { title: opts.title, text: opts.text || opts.subtitle || opts.desc, url: opts.url, imageUrl: opts.imageUrl };
      var call;
      try { call = Promise.resolve(nb.share(req)); } catch (e) { return done({ ok: false, err: String(e && e.message || e) }); }
      call.then(function (r) {
        done(r && r.ok ? { ok: true, res: r } : { ok: false, err: (r && r.error) || 'cancelled' });
      }, function (e) { done({ ok: false, err: String(e && e.message || e) }); });
    });
  }

  // ─── TikTok missions: tiktok_shortcut / tiktok_profile ────────────────────
  // The player is sent off with tiktokMission.start(); the reward is paid
  // when TikTok later confirms it (opened from the icon / came in from the
  // profile) — checked after login and on every return to the app.

  var MISSIONS = {
    shortcut: { start: 'addShortcut', check: 'getShortcutMissionReward' },
    profile: { start: 'startEntranceMission', check: 'getEntranceMissionReward' }
  };
  var missionBusy = {};
  var missionGiven = {};
  var missionStarted = {};   // the player was sent off this session
  var showHooked = false;

  function checkMission(kind) {
    var key = 'tiktok_' + kind;
    if (ready && !loginDone) return Promise.resolve(false);   // wait for the dashboard's values and the cloud claims
    if (featureOff('tiktok_missions')) return Promise.resolve(false);
    var e = entry(key);
    if (!giveCb || !e || isEmpty(e.items) || missionBusy[kind] || missionGiven[kind] || isClaimed(key, e.limit)) return Promise.resolve(false);
    missionBusy[kind] = true;
    return callTikTok(MISSIONS[kind].check, null, 10000).then(function (r) {
      missionBusy[kind] = false;
      if (!r.ok) return false;
      var res = r.res || {};
      var flag = res.canReceiveReward !== undefined ? res.canReceiveReward : res.can_receive_reward;
      // An explicit `true` pays. Some TikTok builds answer success with no
      // flag at all — that counts only after the player was actually sent
      // off this session (what the SDK's own missions rely on), never at a
      // cold start, where it would pay a mission nobody did.
      var can = flag === true || (flag === undefined && !!missionStarted[kind]);
      if (!can) return false;
      if (missionGiven[kind] || isClaimed(key, e.limit)) return false;
      // Locked for the session before the game runs, so a game that gives and
      // then throws in its UI code is not paid on every return to the app;
      // persisted only when onGive did not throw.
      missionGiven[kind] = true;
      if (!give(e.items, key)) return false;
      recordClaim(key);
      return true;
    });
  }

  function checkMissions() {
    return Promise.all([checkMission('shortcut'), checkMission('profile')]).then(function () {});
  }

  var lastActiveCheck = 0;

  /** Back in the foreground: missions, and — at most once a minute — "is this still the active device?". */
  function onAppShow() {
    resumeFrom('app');
    checkMissions();
    // A pending Google payment (cash, bank) that completed meanwhile: credit and
    // finish it now — Google refunds one not finished within 3 days. Not while
    // a purchase sheet is open: that sheet itself hides and shows the app.
    if (loginDone && !buyingGoogle && billing()) recoverGoogle();
    if (!sdk || !ready || !sdk.isAuthenticated || Date.now() - lastActiveCheck < 60000) return;
    lastActiveCheck = Date.now();
    // Any session call does: if another device logged in meanwhile, the SDK
    // gets a 401, marks the session replaced and the kit fires otherDevice.
    // Pending rewards is the call an app should make on resume anyway.
    safe(function () { sdk.iap.checkPendingRewards(); });
  }

  function hookShow() {
    if (showHooked) return;
    var t = root && root.tt;
    // Both or neither: a hide with no matching show would pause for good.
    if (t && typeof t.onShow === 'function' && typeof t.onHide === 'function') {
      showHooked = true;
      safe(function () { t.onShow(onAppShow); });
      // The profile is written when the app is hidden, not only on its timer.
      safe(function () { t.onHide(onAppHide); });
    }
    var doc = safe(function () { return root && root.document; }, null);
    if (!showHooked && doc && typeof doc.addEventListener === 'function') {
      showHooked = true;
      safe(function () {
        doc.addEventListener('visibilitychange', function () {
          if (doc.visibilityState === 'hidden') onAppHide(); else onAppShow();
        });
      });
    }
  }

  function onAppHide() {
    if (P && P.timer) writeProfileNow();
    pauseFor('app');
  }

  // ─── Ads ──────────────────────────────────────────────────────────────────

  var adLabels = {};    // places the game asked showAd / canShowAd about this session
  var shareKeys = { share: true };
  var shareBusy = false;

  function adConfigured(label) {
    if (!sdk || !ready || !label) return false;
    var ads = sdk.ads;
    return safe(function () { return !!ads.getPlacement(label) && ads.resolvePlace(label).resolved; }, false);
  }

  /** An ad place: one the dashboard has, or one the game shows ads at. Its reward is showAd's to pay. */
  function isAdPlace(key) {
    if (has(adLabels, key)) return true;
    return !!(sdk && ready && safe(function () { return sdk.ads.getPlacement(key); }, null));
  }

  /** The place gives a reward with a once / daily limit, and it is used up. */
  function rewardUsedUp(label) {
    var e = entry(label);
    return !!(e && !isEmpty(e.items) && e.limit !== 'always' && isClaimed(label, e.limit));
  }

  /** The dashboard has an ad place with an active unit, and this runtime can show ads. */
  function anyAdPlace() {
    if (!sdk || !ready) return false;
    var canShow = canDo('rewardedVideoAd') || canDo('interstitialAd') || safe(function () { return sdk.isTestMode; }, false);
    return canShow && safe(function () {
      return sdk.ads.getPlaceLabels().length > 0 && sdk.ads.getActivePlacements().length > 0;
    }, false);
  }

  var adToken = 0;

  /** What a finished ad gives: null (failed / skipped / not given), {} (no reward here) or the items. */
  function adOutcome(label, r) {
    if (!r || !r.success) { HSGame.lastAdError = (r && r.error_message) || 'unavailable'; return null; }
    if (!r.completed) { HSGame.lastAdError = 'skipped'; return null; }
    var e = entry(label);
    if (!e || isEmpty(e.items)) return {};         // e.g. an interstitial: shown, nothing to give
    var got = payout(label);
    // A rewarded ad that completed but gave nothing (onGive threw) must not
    // look like the no-reward {} — the game would continue as if paid.
    if (!got) { HSGame.lastAdError = 'not given'; return null; }
    return got;
  }

  // ─── Store gate ───────────────────────────────────────────────────────────
  // TikTok products cost beans and are paid through TikTok. An Android app
  // without its own billing must never list them.

  var shopCount = 0;    // products in the last shop() answer — has('shop')
  var shopKnown = false;  // a shop() answer arrived this session
  var shopTriedAt = 0;

  function storeOpen() {
    // Android: the app's own Google Play billing (TikTok products never show there).
    return !!(sdk && ready) && (platformName() !== 'android' || !!billing());
  }

  var HSGame = {
    version: VERSION,
    debug: false,
    /** Why the last showAd() gave null: 'not configured', 'skipped', 'busy', or TikTok's message. */
    lastAdError: '',
    /** Why the last share() gave null: 'unsupported', 'claimed' (shared, reward already taken), or TikTok's message. */
    lastShareError: '',

    get ready() { return ready; },
    get loggedIn() { return !!(sdk && ready && sdk.isAuthenticated); },
    get openId() { return sdk && ready ? sdk.openId : null; },
    /** The raw HSTikTokSDK, for anything this file does not wrap. */
    get sdk() { return ready ? sdk : null; },
    get trace() { return trace.slice(); },
    /** The defaults passed to start() — read by hs-check. */
    get defaults() { return copy(defaults); },
    /** True when rewards have somewhere to go: an onGive, or a profile to credit. */
    get canGive() { return !!giveCb || !!P; },
    /** 'minis' (TikTok) | 'android' (the HS Android app) | 'browser' (development). For logs — build UI with has(). */
    get platform() { return platformName(); },
    /** True between 'pause' and 'resume' (an ad, a purchase, a share sheet, the app away). */
    get paused() { return !isEmpty(pauseReasons); },

    /**
     * Is this feature on HERE, right now? Show its button / popup only when
     * true, and ask every time you draw (it changes after start() resolves):
     *   'tiktok_missions' — Entry Reward (profile) + Launch Reward (home screen). TikTok only.
     *   'share'           — a share button
     *   'ads'             — any ad button (then canShowAd(place) per button)
     *   'shop'            — the shop button (products exist and this platform can sell)
     *   'cloud'           — "your progress is saved to your account" (login works here)
     * The dashboard can switch any of them off: iaa_config "features": { "share": false }.
     */
    has: function (feature) {
      feature = String(feature || '');
      noteOnce('has:' + feature);
      if (featureOff(feature)) return false;
      switch (feature) {
        case 'tiktok_missions':
          return platformName() === 'minis' && (HSGame.tiktokMission.supported('profile') || HSGame.tiktokMission.supported('shortcut'));
        case 'share': return HSGame.canShare();
        case 'ads': return anyAdPlace();
        case 'shop':
          // The products could not be read (offline at start): ask again, at most once a minute.
          if (storeOpen() && !shopKnown && Date.now() - shopTriedAt > 60000) HSGame.shop();
          return storeOpen() && shopCount > 0;
        case 'cloud': return loginPossible();
      }
      return false;
    },

    /**
     * hs-check only (inert unless the checker set __HS_CHECK__): would onGive
     * accept this key's reward? Hands the items over without recording a claim.
     */
    _probe: function (key) {
      if (!(root && root.__HS_CHECK__)) return null;
      var e = entry(String(key || ''));
      if (!e || isEmpty(e.items)) return { empty: true };
      return { items: copy(e.items), given: give(e.items, 'hs-check:' + key) };
    },

    /**
     * Start everything. Call once at startup. Resolves { loggedIn, reason };
     * never rejects. Rewards work from `defaults` even before (and without) login.
     */
    start: function (opts) {
      opts = opts || {};
      note('start');
      if (started) return Promise.resolve({ loggedIn: HSGame.loggedIn, reason: 'already started' });
      started = true;
      HSGame.debug = !!opts.debug;
      if (typeof opts.onGive === 'function') giveCb = opts.onGive;
      if (typeof opts.onLoad === 'function') loadCb = opts.onLoad;
      var d = opts.defaults || {};
      defaults = {
        rewards: d.rewards && typeof d.rewards === 'object' ? copy(d.rewards) : {},
        items: d.items && typeof d.items === 'object' ? copy(d.items) : {}
      };
      if (!giveCb && !P) log('start() without onGive or a profile — nothing can be given');
      hookShow();

      // Each platform is its own HS game: the Android app's build injects that
      // game's credentials, which win over the TikTok ones written in game.js.
      // In the app, ONLY the injected pair: falling back to game.js would talk
      // to the TikTok game (its ad ids, its players), and a half-injected pair
      // would sign every request with the wrong key.
      var nb = nativeBridge();
      var check = root && root.__HS_CHECK__;   // stand-in credentials for hs-check only
      var gameId, sdkKey;
      if (nb) {
        var injected = (nb.config && typeof nb.config === 'object') ? nb.config : {};
        gameId = String(injected.gameId || '');
        sdkKey = String(injected.sdkKey || '');
        if (!gameId || !sdkKey) gameId = sdkKey = '';   // → offline below, with its own reason
      } else {
        // hs-check runs against its own fake backend: its stand-ins win over
        // whatever is in game.js (empty, a placeholder, or the real pair).
        gameId = String((check && check.gameId) || opts.gameId || '');
        sdkKey = String((check && check.sdkKey) || opts.sdkKey || '');
      }

      var offline = function (reason) { loginDone = true; checkMissions(); return Promise.resolve({ loggedIn: false, reason: reason }); };
      if (!sdk) return offline(loadError || 'SDK not loaded');
      if (!gameId || !sdkKey) return offline(nb ? 'the app was built without its HS game credentials' : 'gameId / sdkKey not set');

      var ok = safe(function () {
        // single: one active device per account. When another device logs in,
        // the SDK stops instead of logging in again (which would knock that
        // device out in turn); the game hears it as otherDevice.
        if (!sdk.init({ gameId: gameId, sdkKey: sdkKey, enableDebugLogs: HSGame.debug, sessionReplaced: 'report' })) return false;
        sdk.registerSyncProvider(cloud);
        sdk.registerRewardHandler({ onOrderRewardsDelivered: onOrder });
        // The cloud is settled by a SUCCESSFUL login only — the startup one or
        // a later one (a buy() after a failed start). The SDK hands the cloud
        // copy over right after this event, so settle on the next tick. A failed
        // login settles nothing: a fresh install must not upload its empty
        // state, and the real cloud copy must still be read when login works.
        sdk.on('loginSuccess', function (profileJson, serverTs) {
          // The login's server time corrects a clock that is BEHIND, before the
          // first sync does: a change stamped too early loses a 'latest' merge
          // it should win. Only forward: by contract it is the time of the last
          // cloud write, which may be old (the HS backend sends "now").
          if (serverTs > 0 && serverTs * 1000 > Date.now() + clockOffset) clockOffset = serverTs * 1000 - Date.now();
          if (serverTs > 0) baseTs = serverTs;
          if (!P) {
            var id = String(sdk.openId || '');
            if (id && id !== saveOwner) {
              cloudOrders = {};
              if (decided && !profileJson) {
                // 3.0: signed in to an account with no cloud copy of its own
                // (a first Google sign-in in the Android app): this phone's
                // progress — and the orders / purchases in it — becomes that
                // account's, and goes up.
                saveOwner = id;
                writeSave(true);
                cloudDirty = true;
              } else {
                // Another account with its own copy (or the session's first
                // login): its copy and cloud copy, never the previous lists.
                if (decided && cloudSettled) acceptNextCloud = true;
                decided = false;
                orders0 = []; ordersNew = []; gpNew = [];
                saveOwner = id;
              }
            }
            if (id) storeSet(SAVE_KEY + '.last', id);
            // No cloud copy at all: this phone's own copy (if any) is the account's.
            if (!profileJson && (!decided || takingOver)) decideWithoutCloud();
            // A copy not in the cloud yet (also one played offline earlier this
            // session) goes up within a second, not at the 10 s tick.
            var unsent = readSave();
            if (!profileJson && unsent && unsent.dirty) { cloudDirty = true; syncSoon(); }
          }
          var switched = onAccount(sdk.openId);   // a different account → its own profile
          if (switched) cloudOrders = {};         // that account's cloud copy says which orders it holds
          // The cloud copy (if any) is handed over synchronously right after
          // this event; past that, nothing more to accept from this login.
          setTimeout(function () {
            acceptNextCloud = false;
            // A cloud copy that could not be read: chosen as if there were none —
            // this phone's own copy, not the game's state at boot (maybe defaults).
            if (!P && !decided) decideWithoutCloud();
            // An account with no cloud copy never reached the merge: its device
            // copy is the account's state now, not a "fresh install" any more…
            if (P) { P.joining = false; if (!conflict) P.fresh = false; }
            settleCloud();
            // …and it goes up, even if nothing changes after the switch.
            if (switched && cloudWanted()) cloud.isDirtyForCloud = true;
            flushGoogleReports();               // purchases made before this session had one
            if (recoverWanted) recoverGoogle(); // it waited for this cloud copy
          }, 0);
        });
        // The server's time of each cloud save corrects this phone's clock, so
        // a wrong clock cannot win a 'latest' merge.
        sdk.on('syncSuccess', function (serverTs) {
          if (serverTs > 0) clockOffset = serverTs * 1000 - Date.now();
        });
        sdk.on('sessionReplaced', function () {
          note('otherDevice');
          cloud.isDirtyForCloud = false;
          kitEmit('otherDevice');
        });
        return true;
      }, false);
      if (!ok) return offline('init failed — check gameId / sdkKey');
      ready = true;

      var finish = function (r) {
        if (r.loggedIn) settleCloud();
        loginDone = true;
        checkMissions();
        // Products are known when start() resolves, so has('shop') is right
        // from the first frame of the menu. Android: Google purchases left
        // unfinished (a crash) are credited now, and queued reports sent.
        var products = storeOpen() ? HSGame.shop() : null;
        return Promise.resolve(products)
          .then(function () { return billing() ? recoverGoogle() : null; })
          .then(function () { flushGoogleReports(); return r; }, function () { return r; });
      };
      // No login (none on this platform, or it failed): the dashboard's ad
      // places, rewards and features still come — they need no account.
      var withoutLogin = function (r) {
        decideOffline();             // 3.0: saves from here on are kept for the last account
        var loading = safe(function () { return sdk.ads.loadRemoteConfig(); }, null);
        return Promise.resolve(loading).then(null, function () {}).then(function () { return finish(r); });
      };
      if (!loginPossible()) return withoutLogin({ loggedIn: false, reason: 'no login on this platform' });
      return sdk.auth.login().then(function (r) {
        if (!r.success) log('login failed: ' + r.failure + ' ' + (r.error || ''));
        var res = { loggedIn: !!r.success, reason: r.success ? '' : (r.failure + ': ' + (r.error || '')) };
        return r.success ? finish(res) : withoutLogin(res);
      }, function (e) {
        return withoutLogin({ loggedIn: false, reason: String(e && e.message || e) });
      });
    },

    // ─── Rewards ─────────────────────────────────────────────

    /**
     * A game moment completed (a mission, a quest, a daily gift, a level
     * bonus…). Its reward — the dashboard's, else the default — goes to
     * onGive. Returns the items given (to show a message), or null: not
     * configured, nothing in it, already claimed (once / today), or onGive threw.
     */
    claim: function (key) {
      key = String(key || '');
      note('claim:' + key);
      if (has(TIKTOK_KEYS, key)) { log('claim("' + key + '") refused — TikTok missions pay themselves when TikTok confirms'); return null; }
      // An ad place's reward is paid by showAd, the share reward by share():
      // claiming them here would pay without the ad / share, or pay twice.
      if (isAdPlace(key) || has(shareKeys, key)) { log('claim("' + key + '") refused — it is paid by ' + (has(shareKeys, key) ? 'share()' : 'showAd()')); return null; }
      // Before login lands, the cloud's claim record (a reinstall) and the
      // dashboard's values are not here yet — a "once" could pay twice.
      if (ready && !loginDone) { log('claim("' + key + '") refused — call it after HSGame.start() resolves'); return null; }
      return payout(key);
    },

    /** The items a key would give — for labels like "Reward: 2 hints". Null when it gives nothing. */
    rewards: function (key) {
      noteOnce('rewards:' + key);
      var e = entry(String(key || ''));
      return e && !isEmpty(e.items) ? copy(e.items) : null;
    },

    /** True when claim(key) would give something now — for "!" badges and enabled buttons. */
    available: function (key) {
      key = String(key || '');
      noteOnce('available:' + key);
      var e = entry(key);
      if (!e || isEmpty(e.items)) return false;
      if (ready && !loginDone) return false;
      if (has(TIKTOK_KEYS, key)) return HSGame.tiktokMission.supported(TIKTOK_KEYS[key]) && !missionGiven[TIKTOK_KEYS[key]] && !isClaimed(key, e.limit);
      return !isClaimed(key, e.limit);
    },

    /** The item catalog entry: { category, name, icon, ... } — dashboard over defaults. */
    item: function (id) { var c = catalog(); return has(c, id) ? copy(c[id]) : null; },
    /** Every item: { id: { category, name, ... } }. */
    items: function () { return copy(catalog()); },

    // ─── Ads ─────────────────────────────────────────────────

    /** True when an ad is set up for this place right now — show / hide the button with it, every time it is drawn. */
    canShowAd: function (label) {
      noteOnce('canShowAd:' + label);
      adLabels[label] = true;
      if (adBusySince && Date.now() - adBusySince < adStaleMs()) return false;
      if (rewardUsedUp(label)) return false;   // a once / daily ad reward already taken: do not offer the ad
      return !featureOff('ads') && adConfigured(label);
    },

    /**
     * Show the ad set up for this place in the dashboard. Resolves:
     *   null — no ad here (not configured, cooling down, no fill), or closed early
     *   {}   — the ad completed and this place gives no reward (e.g. interstitial)
     *   { hint: 1 } — completed, and the reward went to onGive
     * The game never needs to know whether the place is rewarded or interstitial.
     */
    showAd: function (label) {
      label = String(label || '');
      note('showAd:' + label);
      adLabels[label] = true;
      HSGame.lastAdError = '';
      if (adBusySince && Date.now() - adBusySince < adStaleMs()) { HSGame.lastAdError = 'busy'; return Promise.resolve(null); }
      if (!sdk || !ready || featureOff('ads')) { HSGame.lastAdError = 'not configured'; return Promise.resolve(null); }
      // Never make a player watch an ad whose reward they already took.
      if (rewardUsedUp(label)) { HSGame.lastAdError = 'claimed'; return Promise.resolve(null); }

      // This call owns the ad slot until it ends; a stale call that answers
      // late can never unfreeze or unlatch a newer one.
      var token = ++adToken;
      adBusySince = Date.now();
      var endAd = function () { if (token !== adToken) return; adBusySince = 0; resumeFrom('ad'); };

      // No config yet (no login): fetch it BEFORE freezing the game, so a dead
      // connection or a place with no ad never pauses anything.
      var loaded = safe(function () { return sdk.ads.isConfigLoaded; }, false);
      var asked = Date.now();
      var config = loaded ? Promise.resolve() : Promise.resolve(safe(function () { return sdk.ads.loadRemoteConfig(); }, null)).then(null, function () {});
      return config.then(function () {
        // A config that came too late (or after this call went stale) must not
        // start an ad: it would appear long after the tap.
        if (token !== adToken) return null;
        if (Date.now() - asked > AD_TAP_MS) { HSGame.lastAdError = 'not ready'; endAd(); return null; }
        if (!adConfigured(label)) {
          HSGame.lastAdError = safe(function () { return sdk.ads.getPlacement(label); }, null) ? 'cooling down' : 'not configured';
          endAd();
          return null;
        }
        pauseFor('ad');
        return new Promise(function (resolve) {
          var settled = false;
          var timer = setTimeout(function () {
            if (settled) return;
            settled = true;
            HSGame.lastAdError = 'timeout';
            endAd();
            resolve(null);
          }, adStaleMs());
          var showing;
          try { showing = Promise.resolve(sdk.ads.showAdsRemote(label)); } catch (e) { showing = Promise.reject(e); }
          showing.then(function (r) {
            var late = settled;
            settled = true;
            clearTimeout(timer);
            endAd();
            var out = adOutcome(label, r);
            // A late answer still pays an ad that was watched — the reward goes
            // to the profile / onGive; only the promise already said null.
            if (!late) resolve(out);
          }, function (e) {
            var late = settled;
            settled = true;
            clearTimeout(timer);
            endAd();
            if (late) return;
            HSGame.lastAdError = String(e && e.message || e);
            resolve(null);
          });
        });
      });
    },

    // ─── Share ───────────────────────────────────────────────

    /** True when sharing works here: TikTok 40.3.0+, or the Android app's share sheet. */
    canShare: function () {
      if (featureOff('share')) return false;
      var nb = nativeBridge();
      return nb ? typeof nb.share === 'function' : !!tiktok('shareAppMessage');
    },

    /**
     * Open the share sheet (TikTok's, or Android's in the app): opts { title,
     * subtitle, imageUrl, templateType }. Resolves like showAd:
     *   null        — not shared (cancelled, unsupported — see lastShareError)
     *   {}          — shared; this key gives nothing here (none set, or today's taken)
     *   { hint: 3 } — shared, and the reward of `key` (default "share", once a day) was given
     * A shared result (not null) can also complete the game's own tasks:
     *   HSGame.share({...}).then(function (r) { if (r) { shares++; if (shares === 3) HSGame.claim('quest_share_3'); } });
     */
    share: function (opts, key) {
      key = String(key || 'share');
      note('share:' + key);
      shareKeys[key] = true;
      HSGame.lastShareError = '';
      if (featureOff('share')) { HSGame.lastShareError = 'unsupported'; return Promise.resolve(null); }
      // Before login lands a reinstall's claims are not back yet — a daily
      // share could pay twice. And one sheet at a time.
      if (ready && !loginDone) { HSGame.lastShareError = 'not ready'; return Promise.resolve(null); }
      if (shareBusy) { HSGame.lastShareError = 'busy'; return Promise.resolve(null); }
      shareBusy = true;
      pauseFor('share');
      // The player picks friends in TikTok's sheet: give it time, but not forever.
      var sharing = nativeBridge() ? shareNative(opts || {}) : callTikTok('shareAppMessage', opts || {}, 120000);
      return sharing.then(function (r) {
        shareBusy = false;
        resumeFrom('share');
        if (!r.ok) { HSGame.lastShareError = r.err; return null; }
        // Shared. Like showAd: {} = done, nothing given here (no reward for this
        // key on this platform, or today's is taken) — the game can still count
        // it toward its own tasks and claim('its_task_key').
        var e = entry(key);
        if (!e || isEmpty(e.items)) return {};
        var items = payout(key);
        if (!items) { HSGame.lastShareError = isClaimed(key, e.limit) ? 'claimed' : 'not given'; return {}; }
        return items;
      });
    },

    // ─── TikTok missions ─────────────────────────────────────

    tiktokMission: {
      /** "shortcut" (add to home screen) or "profile" (visit from the TikTok profile). */
      supported: function (kind) { var m = MISSIONS[kind]; return !!(m && !featureOff('tiktok_missions') && tiktok(m.start)); },
      /** Already rewarded — remove the "!" badge. */
      done: function (kind) {
        var key = 'tiktok_' + kind;
        var e = entry(key);
        return !!missionGiven[kind] || isClaimed(key, e ? e.limit : 'once');
      },
      /** Button tap: send the player to do it. Resolves 'started' | 'unsupported' | 'failed'. */
      start: function (kind) {
        note('tiktokMission:' + kind);
        var m = MISSIONS[kind];
        if (!m) return Promise.resolve('unsupported');
        return callTikTok(m.start, null, 120000).then(function (r) {
          if (r.ok) { missionStarted[kind] = true; checkMissions(); }
          return r.ok ? 'started' : (r.err === 'unsupported' ? 'unsupported' : 'failed');
        });
      },
      /** Ask TikTok now (also done after login and on every return to the app). */
      refresh: function () { return checkMissions(); }
    },

    // ─── Shop ────────────────────────────────────────────────

    /**
     * Products from the HS dashboard: [{ product_id, name, description,
     * beans_cost, items: { hint: 15 }, ...display fields (icon, badge…) }].
     * Works before login.
     */
    shop: function () {
      note('shop');
      if (!storeOpen() || featureOff('shop')) return Promise.resolve([]);
      shopTriedAt = Date.now();
      if (billing()) {
        // Android: products on sale in BOTH the HS dashboard and Google Play,
        // with Google's local price.
        return loadGoogleProducts().then(function (list) {
          shopKnown = true;
          shopCount = list.length;
          if (recoverWanted) recoverGoogle();     // start-up was offline: recover now
          return list;
        }, function () { return []; });
      }
      return sdk.iap.getShopItems().then(function (r) {
        if (!r.success) return [];
        shopKnown = true;
        var list = (r.data || []).map(function (p) {
          var out = {};
          for (var k in p) if (has(p, k) && k !== 'rewards') out[k] = p[k];
          out.items = toItems(p.rewards);
          return out;
        });
        shopCount = list.length;
        return list;
      }, function () { return []; });
    },

    /**
     * Buy a product. Resolves { ok, error, delivered }. The items arrive in
     * onGive — never give them here. ok + !delivered: paid, but this build
     * could not give it (unknown item, onGive threw) — it is kept and comes
     * back at the next start; tell the player it is on its way.
     */
    buy: function (productId) {
      note('buy');
      if (!storeOpen() || featureOff('shop')) return Promise.resolve({ ok: false, error: 'Store unavailable', delivered: false });
      if (billing()) return buyGoogle(productId);
      lastBuyGiven = null;
      // Frozen while the pay sheet is up — not during the settlement polling
      // after it closed, and never longer than BUY_PAUSE_MAX_MS.
      pauseFor('buy');
      var unpause = function () { clearTimeout(cap); safe(function () { offClosed(); }); resumeFrom('buy'); };
      var cap = setTimeout(unpause, BUY_PAUSE_MAX_MS);
      var offClosed = safe(function () { return sdk.on('paymentUiClosed', unpause); }, null) || function () {};
      var buying;
      try { buying = Promise.resolve(sdk.iap.buyProduct(String(productId))); } catch (e) { buying = Promise.reject(e); }
      return buying.then(
        function (r) {
          unpause();
          var ok = !!(r && r.success);
          // Login recovery handed this very order over while it was being
          // polled: the items DID arrive (through onGive / the profile).
          if (!ok && r && /already delivered/i.test(String(r.error || ''))) return { ok: true, error: '', delivered: true };
          return { ok: ok, error: ok ? '' : ((r && r.error) || 'Purchase failed'), delivered: ok && lastBuyGiven !== false };
        },
        function (e) { unpause(); return { ok: false, error: String(e && e.message || e), delivered: false }; }
      );
    },

    // ─── Cloud save ──────────────────────────────────────────

    // ─── Profile (3.1) ───────────────────────────────────────

    /**
     * The game's progress, owned by the kit. Call once, BEFORE start():
     *
     *   var profile = HSGame.profile({ level: 0, coins: 0, hint: 3, sound: true }, {
     *     save: 'cloud',               // 'local' = this device only · 'cloud' = device + cloud (default)
     *     local: ['sound'],            // fields that stay on this device
     *     merge: { level: 'max' },     // 'max' | 'min' for values that only move one way; default 'latest'
     *     version: 1, migrate: function (old, fromVersion) { return old; }   // when the layout changes
     *   });
     *   profile.get('coins'); profile.add('coins', 50); profile.set('level', 4); profile.update({...});
     *   profile.on('coins', function (now, before) { redraw(); });   // or '*' for every change
     *
     * Rewards whose item is a number field here (coins, hint…) are credited to
     * it by the kit — onGive is then only needed for other items.
     */
    profile: function (defs, opts) {
      if (P) return P.api;
      opts = opts || {};
      note('profile');
      var local = {};
      (opts.local || []).forEach(function (f) { local[f] = true; });
      P = {
        defs: copy(defs || {}),
        mode: opts.save === 'local' ? 'local' : 'cloud',
        local: local,
        rules: opts.merge && typeof opts.merge === 'object' ? copy(opts.merge) : {},
        version: opts.version | 0,
        summary: typeof opts.summary === 'string' ? opts.summary : '',
        migrate: typeof opts.migrate === 'function' ? opts.migrate : null,
        listeners: {},
        timer: null
      };
      // In cloud mode the device copy belongs to an account; before login the
      // last account that played here is assumed (corrected at login).
      loadProfile(P.mode === 'cloud' ? storeGet(PROFILE_KEY + '.last') : '');
      // Up to 3.1 claims were one record per device. It belongs to the account
      // that played here last — the one just loaded — so it moves to that account.
      if (P.owner && !storeGet(claimsKey())) {
        var legacy = storeGet(CLAIMS_KEY);
        if (legacy) storeSet(claimsKey(), legacy);
      }
      var api = {
        get: function (f) { return copy(P.data[f]); },
        all: function () { return copy(P.data); },
        set: function (f, v) { var c = {}; c[f] = v; applyChanges(c, 'game'); },
        add: function (f, n) { var c = {}; c[f] = (Number(P.data[f]) || 0) + (Number(n) || 0); applyChanges(c, 'game'); },
        update: function (obj) { if (obj && typeof obj === 'object') applyChanges(copy(obj), 'game'); },
        on: function (f, cb) {
          if (typeof cb !== 'function') return function () {};
          (P.listeners[f] = P.listeners[f] || []).push(cb);
          return function () { var l = P.listeners[f] || []; var i = l.indexOf(cb); if (i >= 0) l.splice(i, 1); };
        },
        /** Write to the device now (the kit also does it on a short timer and when the app hides). */
        flush: function () { writeProfileNow(); }
      };
      P.api = api;
      return api;
    },

    /**
     * Kit events: 'otherDevice' (this account was opened on another device —
     * show "Playing on another device · Play here" and call takeOver()), and
     * 'given' (items, from) after any reward, for a "+2 hints" message,
     * 'pause' (reason) / 'resume' — an ad, a purchase or the app going away:
     * mute the music and freeze the game until 'resume'. Fired once per pause
     * however many reasons overlap,
     * 'accountConflict' (info, choose) — a guest who made progress logged in
     * to an account with its own: info { field, device, account }; call
     * choose('account' | 'device') once. Without a listener the kit asks with
     * the system popup. 'accountChosen' (which) after either.
     * Returns an unsubscribe function.
     */
    on: function (name, cb) {
      if (typeof cb !== 'function') return function () {};
      (kitListeners[name] = kitListeners[name] || []).push(cb);
      // Subscribed while already paused: hear that pause, so the 'resume'
      // that follows is not an unmatched one.
      if (name === 'pause' && !isEmpty(pauseReasons)) {
        var why = Object.keys(pauseReasons)[0];
        setTimeout(function () { if (!isEmpty(pauseReasons)) safe(function () { cb(why); }); }, 0);
      }
      return function () { var l = kitListeners[name] || []; var i = l.indexOf(cb); if (i >= 0) l.splice(i, 1); };
    },

    /** True when another device took this account over (until takeOver()). */
    get otherDevice() { return !!(sdk && ready && sdk.isSessionReplaced); },

    /**
     * True while a "Sign in" button makes sense: a guest, or (Android app) a
     * device account that can still sign in to Google Play Games.
     */
    get canSignIn() {
      if (!sdk || !ready || !loginPossible() || featureOff('cloud')) return false;
      if (!HSGame.loggedIn) return true;
      var nb = nativeBridge();
      return !!(nb && typeof nb.login === 'function' && onDeviceAccount());
    },

    /**
     * The "Sign in to save your progress" button: show it only while
     * HSGame.canSignIn. Start-up already tried a silent sign-in; this one may
     * show the platform's sign-in screen (Google Play Games in the Android
     * app). The guest's — or the device account's — progress joins the account,
     * or the player chooses (accountConflict) when the account has its own.
     * Resolves { loggedIn, reason }; never rejects.
     */
    login: function () {
      note('login');
      if (!sdk || !ready) return Promise.resolve({ loggedIn: false, reason: 'SDK not started' });
      if (HSGame.loggedIn && !HSGame.canSignIn) return Promise.resolve({ loggedIn: true, reason: '' });
      if (!loginPossible()) return Promise.resolve({ loggedIn: false, reason: 'no sign-in on this platform' });
      return Promise.resolve(safe(function () { return sdk.auth.login({ interactive: true }); }, null)).then(function (r) {
        var ok = !!(r && r.success);
        return { loggedIn: ok, reason: ok ? '' : ((r && (r.failure + ': ' + (r.error || ''))) || 'sign-in failed') };
      }, function (e) {
        return { loggedIn: false, reason: String(e && e.message || e) };
      });
    },

    /**
     * "Play here": log in again on this device, pull the cloud copy and merge
     * this device's own progress into it, and become the active device. The
     * other device gets otherDevice in turn. Resolves { loggedIn, reason }.
     */
    takeOver: function () {
      note('takeOver');
      if (!sdk || !ready) return Promise.resolve({ loggedIn: false, reason: 'SDK not started' });
      takingOver = true;
      return sdk.auth.login().then(function (r) {
        takingOver = false;
        if (r.success && cloudWanted()) cloud.isDirtyForCloud = true;   // push the merge
        return { loggedIn: !!r.success, reason: r.success ? '' : (r.failure + ': ' + (r.error || '')) };
      }, function (e) {
        takingOver = false;
        return { loggedIn: false, reason: String(e && e.message || e) };
      });
    },

    /** Save progress (3.0 style): the WHOLE small progress object. With HSGame.profile() this is not needed. */
    save: function (data) {
      note('save');
      if (P) { log('save() ignored — this game uses HSGame.profile(); change the profile instead'); return; }
      var c = safe(function () { return JSON.parse(JSON.stringify(data)); }, undefined);
      if (c === undefined || c === null || typeof c !== 'object') { log('save() needs a plain JSON object'); return; }
      latest = c; hasLatest = true;
      // Orders credited before this save are in it now: up soon, so the SDK
      // can confirm them.
      var withOrders = ordersNew.length > 0;
      if (withOrders) { orders0 = trimOrders(orders0.concat(ordersNew)); ordersNew = []; }
      if (cloudSettled) cloud.isDirtyForCloud = true;
      markSaveDirty();                 // on the device until it is in the cloud
      if (withOrders) syncSoon();
    }
  };

  if (typeof module === 'object' && module && module.exports) module.exports = HSGame;
  if (root) root.HSGame = HSGame;
})(typeof GameGlobal !== 'undefined' ? GameGlobal : (typeof globalThis !== 'undefined' ? globalThis : this));

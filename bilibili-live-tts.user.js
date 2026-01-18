// ==UserScript==
// @name         Bilibili 直播 TTS (WebSocket Hook & Filter UI v1.6)
// @namespace    https://github.com/biuuu/Bilibili-Live-TTS
// @version      1.6.1
// @description  通过Hook WebSocket实现B站直播数据过滤和语音播报（弹幕、礼物、SC、上舰、入场等），支持队列、模板、去重、合并、黑白名单、语速音量、外部TTS API、整点报时。
// @author       biuuu & gemini-2.5-pro-exp-03-25
// @match        *://live.bilibili.com/*
// @grant        GM_addStyle
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        unsafeWindow
// @require      https://unpkg.com/pako@2.0.4/dist/pako.min.js
// @run-at       document-start
// @noframes
// ==/UserScript==

(function() {
    'use strict';

    // --- 配置常量 ---
    const SCRIPT_PREFIX = 'bili_live_tts_';
    const GIFT_COMBO_TIMEOUT = 1000;
    const DEFAULT_SETTINGS = {
        enabled: false,
        ttsEngine: 'browser',
        externalTtsUrlTemplate: 'https://your-tts-api.com/speak?text={encodedText}',
        selectedVoice: '',
        speechRate: 1.0,
        speechVolume: 1.0,
        hourlyChimeEnabled: false, // 新增：整点报时开关
        hourlyChimeTemplate: '现在是{hour}点整', // 新增：报时模板
        globalBlockUserIds: '',
        globalBlockKeywords: '',
        filters: {
            danmu: {
                enabled: true,
                contentKeywords: '',
                contentKeywordsBlock: '',
                hasMedal: false,
                minMedalLevel: 0,
                danmuDebounceEnabled: true,
                danmuDebounceTime: 30,
            },
            gift: { enabled: true, minPrice: 0.1, hasMedal: false, minMedalLevel: 0 },
            superchat: { enabled: true, minPrice: 1, hasMedal: false, minMedalLevel: 0 },
            guard: { enabled: true, level3: true, level2: true, level1: true },
            interact: { enabled: false, typeEnter: true, typeFollow: true, typeShare: true, hasMedal: false, minMedalLevel: 0 },
        },
        templates: {
            danmu: '{username} 说: {text}',
            gift: '{username} {action} {count}个 {giftName}',
            superchat: '{username} 发送 {price}元SC {text}',
            guard: '欢迎 {username} 开通{num}{unit}{levelName}',
            interact: '{username} {actionText}',
        }
    };

    // --- 状态变量 ---
    let settings = DEFAULT_SETTINGS;
    let voices = [];
    let brotliDecode; let brotliReady = false; const brotliQueue = [];
    const synth = window.speechSynthesis;
    const ttsQueue = []; let isSpeaking = false; let currentAudioElement = null;
    const recentSuperchatIds = new Map(); const recentDanmu = new Map(); const recentGiftCombos = new Map();
    let hourlyChimeTimeoutId = null; // 新增：报时 Timeout ID
    const userCache = new Map(); // 新增：用户ID到用户名的缓存

    // --- Brotli 加载 (代码同前) ---
    try { import("https://unpkg.com/brotli-wasm@3.0.1/index.web.js?module").then(b=>b.default).then(b=>{brotliDecode=b.decompress;brotliReady=true;while(brotliQueue.length>0){const{event,ws}=brotliQueue.shift();handleMessage(event,ws);}}).catch(e=>console.error("[Bili TTS] Brotli fail:",e)); } catch(e){console.error("[Bili TTS] Import Brotli fail:",e);}

    // --- Protobuf 简易解码器 (用于解析 INTERACT_WORD_V2) ---
    const ProtoUtils = {
        decodeBase64: (str) => {
            const s = window.atob(str);
            const bytes = new Uint8Array(s.length);
            for (let i = 0; i < s.length; i++) bytes[i] = s.charCodeAt(i);
            return bytes;
        },
        readVarint: (buf, offset) => {
            let res = 0n, shift = 0n;
            let count = 0;
            while (true) {
                const b = buf[offset + count];
                count++;
                res |= BigInt(b & 0x7F) << shift;
                shift += 7n;
                if ((b & 0x80) === 0) break;
            }
            return { value: res, length: count };
        },
        readString: (buf, offset, len) => {
            return new TextDecoder().decode(buf.slice(offset, offset + len));
        },
        parse: (buf) => {
            const res = {};
            let off = 0;
            while (off < buf.length) {
                const { value: tag, length: tagLen } = ProtoUtils.readVarint(buf, off);
                off += tagLen;
                const field = Number(tag >> 3n);
                const type = Number(tag & 7n);
                if (type === 0) {
                    const { value, length } = ProtoUtils.readVarint(buf, off);
                    off += length;
                    res[field] = value;
                } else if (type === 2) {
                    const { value: lenBig, length: lenLen } = ProtoUtils.readVarint(buf, off);
                    const len = Number(lenBig);
                    off += lenLen;
                    res[field] = { start: off, length: len, buffer: buf };
                    off += len;
                } else if (type === 5) off += 4;
                else if (type === 1) off += 8;
                else break;
            }
            return res;
        }
    };

    // --- WebSocket Hook (代码同前) ---
    const originalWebSocket=unsafeWindow.WebSocket; unsafeWindow.WebSocket=function(...a){const w=new originalWebSocket(...a);w.binaryType='arraybuffer';const l=function(e){if(e.data instanceof ArrayBuffer){const d=new DataView(e.data);if(e.data.byteLength<16)return; const p=d.getUint16(6);if(p===3){if(brotliReady)handleMessage(e,w);else brotliQueue.push({event:e,ws:w});}else handleMessage(e,w);}}; w.addEventListener('message',l); w.addEventListener('close',()=>w.removeEventListener('message',l)); w.addEventListener('error',(r)=>{console.error('[Bili TTS] WS Error:',r);w.removeEventListener('message',l);}); return w;}; unsafeWindow.WebSocket.prototype=originalWebSocket.prototype; unsafeWindow.WebSocket.prototype.constructor=unsafeWindow.WebSocket; for(let k in originalWebSocket)if(originalWebSocket.hasOwnProperty(k)){try{unsafeWindow.WebSocket[k]=originalWebSocket[k];}catch(e){}}

    // --- 消息解码 (代码同前) ---
    function decodeMessage(b){const d=new DataView(b);const pL=d.getUint32(0);const hL=d.getUint16(4);const pV=d.getUint16(6);const op=d.getUint32(8);if(pL<hL||pL>b.byteLength)return null;const bd=b.slice(hL,pL);try{switch(pV){case 0:return JSON.parse(new TextDecoder().decode(bd));case 1:if(op===3&&bd.byteLength>=4)return{cmd:'POPULARITY',popularity:new DataView(bd).getUint32(0)};else if(op===8)return JSON.parse(new TextDecoder().decode(bd));return null;case 2:{const t=new TextDecoder().decode(pako.inflate(new Uint8Array(bd)));const m=[];let s=0,c=0,iS=false;for(let i=0;i<t.length;i++){const h=t[i];if(h==='"'&&(i===0||t[i-1]!=='\\'))iS=!iS;if(!iS){if(h==='{'){if(c===0)s=i;c++;}else if(h==='}'){c--;if(c===0&&s!==-1){try{m.push(JSON.parse(t.substring(s,i+1)));}catch(e){}s=-1;}}}}return m.length>0?m:null;} case 3:{if(!brotliDecode)return null;const dec=brotliDecode(new Uint8Array(bd));let o=0;const ms=[];while(o<dec.length){const pV=new DataView(dec.buffer,dec.byteOffset+o);const sL=pV.getUint32(0);const sH=pV.getUint16(4);if(o+sL>dec.length||sL<sH){break;}const sB=dec.slice(o+sH,o+sL);try{ms.push(JSON.parse(new TextDecoder().decode(sB)));}catch(e){} o+=sL;}return ms.length>0?ms:null;} default:return null;}}catch(e){console.error("[Bili TTS] Decode Err:",e);return null;}}

    function updateUserCache(uid, username) {
        if (uid && username && !username.includes('...')) {
            userCache.set(uid, username);
            if (userCache.size > 2000) {
                 const firstKey = userCache.keys().next().value;
                 userCache.delete(firstKey);
            }
        }
    }

    // --- 消息处理与分发 (代码同前 v1.5) ---
    function handleMessage(e,w){if(!(e.data instanceof ArrayBuffer))return;let d;try{d=decodeMessage(e.data);}catch(e){console.error("[Bili TTS] Decode Fail:",e);return;}if(!d)return;const p=(a)=>{if(a&&a.cmd)processData(a);};if(Array.isArray(d))d.forEach(p);else p(d);}
    function processData(data){if(!settings.enabled)return;let speakText=null;let filterCategory=null;let itemData={};let templateKey=null;let shouldProcess=true;let skipImmediateSpeak=false;try{switch(data.cmd){case'DANMU_MSG':{filterCategory='danmu';templateKey='danmu';if(!settings.filters.danmu.enabled){shouldProcess=false;break;}const info=data.info;const text=info[1];const uid=info[2][0];const username=info[2][1];updateUserCache(uid, username);const medalInfo=info[3];const hasMedal=!!(medalInfo&&medalInfo.length>0&&medalInfo[1]);const medalLevel=hasMedal?medalInfo[0]:0;if(settings.filters.danmu.danmuDebounceEnabled){const now=Date.now();const debounceTimeMs=settings.filters.danmu.danmuDebounceTime*1000;if(recentDanmu.has(text)){if(now-recentDanmu.get(text)<debounceTimeMs){shouldProcess=false;break;}}recentDanmu.set(text,now);setTimeout(()=>{if(recentDanmu.get(text)===now)recentDanmu.delete(text);},debounceTimeMs+500);}itemData={type:'danmu',uid,username,text,hasMedal,medalLevel};break;} case'SEND_GIFT':{filterCategory='gift';templateKey='gift';skipImmediateSpeak=true;if(!settings.filters.gift.enabled){shouldProcess=false;break;}const d=data.data;const uid=d.uid;const username=d.uname;updateUserCache(uid, username);const giftId=d.giftId;const giftName=d.giftName;const count=d.num;const action=d.action;const totalCoin=d.total_coin;const coinType=d.coin_type;const price=coinType==='gold'?totalCoin/1000:0;const medalInfo=d.medal_info;const hasMedal=!!(medalInfo&&medalInfo.medal_name);const medalLevel=hasMedal?medalInfo.medal_level:0;if(coinType!=='gold'||price<settings.filters.gift.minPrice){shouldProcess=false;break;}const comboKey=`${uid}:${giftId}`;const existingCombo=recentGiftCombos.get(comboKey);if(existingCombo){clearTimeout(existingCombo.timeoutId);existingCombo.count+=count;existingCombo.action=action;const newTimeoutId=setTimeout(()=>{const cData=recentGiftCombos.get(comboKey);if(cData){const fData={type:'gift',...cData};if(!isUserBlocked(fData.uid,fData.username)&&passesCategoryFilters(fData,'gift')){const txt=formatTemplate(settings.templates.gift,fData);if(txt){console.log(`[Bili TTS Speak Queue] ${txt} (Combo)`);queueSpeak(txt);}}recentGiftCombos.delete(comboKey);}},GIFT_COMBO_TIMEOUT);existingCombo.timeoutId=newTimeoutId;}else{const initData={uid,username,giftId,giftName,count,price,hasMedal,medalLevel,action};const timeoutId=setTimeout(()=>{const cData=recentGiftCombos.get(comboKey);if(cData&&cData.count===initData.count){const fData={type:'gift',...cData};if(!isUserBlocked(fData.uid,fData.username)&&passesCategoryFilters(fData,'gift')){const txt=formatTemplate(settings.templates.gift,fData);if(txt){console.log(`[Bili TTS Speak Queue] ${txt} (Single)`);queueSpeak(txt);}}recentGiftCombos.delete(comboKey);}},GIFT_COMBO_TIMEOUT);recentGiftCombos.set(comboKey,{...initData,timeoutId});}shouldProcess=false;break;} case'SUPER_CHAT_MESSAGE':{filterCategory='superchat';templateKey='superchat';if(!settings.filters.superchat.enabled){shouldProcess=false;break;}const d=data.data;const uid=d.uid;const username=d.user_info.uname;updateUserCache(uid, username);const text=d.message;const price=d.price;const scId=d.id;const medalInfo=d.medal_info;const hasMedal=!!(medalInfo&&medalInfo.medal_name);const medalLevel=hasMedal?medalInfo.medal_level:0;const now=Date.now();if(recentSuperchatIds.has(scId)){shouldProcess=false;break;}recentSuperchatIds.set(scId,now);setTimeout(()=>{if(recentSuperchatIds.get(scId)===now)recentSuperchatIds.delete(scId);},1000);if(price<settings.filters.superchat.minPrice){shouldProcess=false;break;}itemData={type:'superchat',uid,username,text,price,scId,hasMedal,medalLevel};break;} case'SUPER_CHAT_MESSAGE_JPN':{shouldProcess=false;break;} case'GUARD_BUY':{filterCategory='guard';shouldProcess=false;break;} case'USER_TOAST_MSG':{filterCategory='guard';templateKey='guard';if(!settings.filters.guard.enabled){shouldProcess=false;break;}const d=data.data;const uid=d.uid;const username=d.username;updateUserCache(uid, username);const level=d.guard_level;const levelName=d.role_name;const num=d.num||1;const unit=d.unit||'';const hasMedal=false;const medalLevel=0;if((level===1&&!settings.filters.guard.level1)||(level===2&&!settings.filters.guard.level2)||(level===3&&!settings.filters.guard.level3)){shouldProcess=false;break;}itemData={type:'guard',uid,username,level,levelName,num,unit,hasMedal,medalLevel};break;} case'INTERACT_WORD_V2':
case'INTERACT_WORD':{filterCategory='interact';templateKey='interact';const d=data.data;

    // 如果存在 pb 字段，尝试进行 Protobuf 解码并填充 d 对象
    if (d.pb) {
        try {
            const pbData = ProtoUtils.parse(ProtoUtils.decodeBase64(d.pb));

            if (pbData[1]) d.uid = Number(pbData[1]); // Tag 1: uid
            if (pbData[2] && pbData[2].buffer) d.uname = ProtoUtils.readString(pbData[2].buffer, pbData[2].start, pbData[2].length); // Tag 2: uname
            if (pbData[5]) d.msg_type = Number(pbData[5]); // Tag 5: msg_type

            // Tag 9: fans_medal (Nested Message)
            if (pbData[9] && pbData[9].buffer) {
                const medalBuf = pbData[9].buffer.slice(pbData[9].start, pbData[9].start + pbData[9].length);
                const medalData = ProtoUtils.parse(medalBuf);
                d.fans_medal = {
                    medal_name: (medalData[1] && medalData[1].buffer) ? ProtoUtils.readString(medalData[1].buffer, medalData[1].start, medalData[1].length) : '',
                    medal_level: (medalData[2] && typeof medalData[2] === 'bigint') ? Number(medalData[2]) : 0,
                    is_lighted: (medalData[6] && typeof medalData[6] === 'bigint') ? Number(medalData[6]) : 1
                };
            }
        } catch (e) {
            console.error('[Bili TTS] PB Decode Error:', e);
        }
    }

    // 兼容 V2 更加复杂的嵌套结构，尝试从不同路径提取 UID 和用户名
    const uid = d.uid || (d.uinfo && d.uinfo.base && d.uinfo.base.uid);
    const username = d.uname || (d.uinfo && d.uinfo.base && d.uinfo.base.name);
    const msgType = d.msg_type;

    if (uid && username) updateUserCache(uid, username);

    if(!settings.filters.interact.enabled){shouldProcess=false;break;}

    // 兼容粉丝勋章路径
    const m = d.fans_medal || (d.uinfo && d.uinfo.medal);
    const hasMedal = !!(m && (m.medal_name || m.name) && (m.is_lighted === 1 || m.is_light === 1));
    const medalLevel = hasMedal ? (m.medal_level || m.level || 0) : 0;

            let actionText='';let typeFlag='';

            if(msgType==1&&settings.filters.interact.typeEnter){actionText='进入直播间';typeFlag='enter';}

            else if(msgType==2){
            if(settings.filters.interact.typeFollow){actionText='关注了主播';typeFlag='follow';}
            else{shouldProcess=false;break;}
        }else if(msgType==3&&settings.filters.interact.typeShare){actionText='分享了直播间';typeFlag='share';}
        else{shouldProcess=false;break;}

        itemData={type:'interact',uid,username,msgType,hasMedal,medalLevel,typeFlag,actionText};break;}

        // --- 新增 DM_INTERACTION 支持 (解决关注不播报) ---
        case 'DM_INTERACTION': {
        const d = data.data;
        const payloadStr = d.payload;
        if (!payloadStr) break;
        try {
            const pl = JSON.parse(new TextDecoder().decode(ProtoUtils.decodeBase64(payloadStr)));
            console.log('[Bili TTS] DM_INTERACTION Payload:', pl);
        } catch(e) {
             try {
                const pbData = ProtoUtils.parse(ProtoUtils.decodeBase64(payloadStr));
                console.log('[Bili TTS] DM_INTERACTION PB Decode:', pbData);
             } catch (e2) {
                 console.log('[Bili TTS] DM_INTERACTION Decode Fail', e, e2);
             }
        }
        break;
    }

    // --- 新增: 尝试从 NOTICE_MSG / SYS_MSG 中提取关注信息 (保底方案) ---
    case 'NOTICE_MSG':
    case 'SYS_MSG': {
        if (!settings.filters.interact.enabled || !settings.filters.interact.typeFollow) break;
        const msg = data.msg_text || data.msg || '';
        // 典型文本: "XXX 关注了主播"
        if (msg.includes('关注了主播')) {
            console.log('[Bili TTS] Fallback Follow Detect:', msg);
            // 尝试提取用户名
            const match = /^(.*?) 关注了主播/.exec(msg);
            if (match) {
                const username = match[1];
                // 构造伪造的 interact 数据
                itemData = {
                    type: 'interact',
                    uid: 0, // 这种消息通常没有 UID
                    username: username,
                    msgType: 2, // 伪造为关注类型
                    hasMedal: false, 
                    medalLevel: 0,
                    typeFlag: 'follow',
                    actionText: '关注了主播'
                };
                filterCategory = 'interact';
                templateKey = 'interact';
                // 跳过后续的 isUserBlocked 检查 (因为没有 UID)
                // 直接在这里处理并 break，或者让它流转下去 (需要注意 UID 0 的处理)
                
                                // 由于下方有 `if(!itemData.uid)` 检查，这里我们需要特殊处理
                                // 或者我们可以给一个伪造的负数 UID 避免被过滤
                                itemData.uid = -1; 
                            }
                        }
                        break;
                    }
    default:shouldProcess=false;break;}}catch(e){console.error("[Bili TTS] Error processing cmd:",data.cmd,e,data);return;} if(!shouldProcess||!itemData.uid||!filterCategory||!templateKey||skipImmediateSpeak)return; if(isUserBlocked(itemData.uid,itemData.username))return; if(passesCategoryFilters(itemData,filterCategory)){speakText=formatTemplate(settings.templates[templateKey],itemData);if(speakText){console.log(`[Bili TTS Speak Queue] ${speakText}`);queueSpeak(speakText);}}}
    // --- Filtering Logic (unchanged from v1.4) ---
    function parseFilterList(str){if(!str)return[];return str.split(/[\n,]+/).map(s=>s.trim().toLowerCase()).filter(s=>s);}
    function isUserBlocked(uid,username){const bIds=parseFilterList(settings.globalBlockUserIds).map(id=>parseInt(id)).filter(id=>!isNaN(id));if(bIds.includes(uid))return true;const bKw=parseFilterList(settings.globalBlockKeywords);const lUn=username?username.toLowerCase():'';if(bKw.some(kw=>lUn.includes(kw)))return true;return false;}
    function passesCategoryFilters(itemData,category){if(!settings.filters[category])return false;const f=settings.filters[category];const{text,hasMedal,medalLevel}=itemData;if(category==='danmu'&&f.contentKeywordsBlock){const bKw=parseFilterList(f.contentKeywordsBlock);const lTxt=text?text.toLowerCase():'';if(bKw.some(kw=>lTxt.includes(kw)))return false;} if(category==='danmu'&&f.contentKeywords){const kws=parseFilterList(f.contentKeywords);const lTxt=text?text.toLowerCase():'';if(kws.length>0&&!kws.some(kw=>lTxt.includes(kw)))return false;} if(f.hasMedal&&!hasMedal)return false;if(f.minMedalLevel>0&&(!hasMedal||medalLevel<f.minMedalLevel))return false;return true;}

    // --- Template Formatting (unchanged from v1.5) ---
    function formatTemplate(t,d){if(!t)return'';let r=t;r=r.replace(/{username}/g,d.username||'');r=r.replace(/{uid}/g,d.uid||'');r=r.replace(/{text}/g,d.text||'');r=r.replace(/{giftName}/g,d.giftName||'');r=r.replace(/{count}/g,d.count||'');r=r.replace(/{price}/g,d.price||'');r=r.replace(/{levelName}/g,d.levelName||'');r=r.replace(/{actionText}/g,d.actionText||'');r=r.replace(/{medalLevel}/g,d.medalLevel||'0');r=r.replace(/{num}/g,d.num||'');r=r.replace(/{unit}/g,d.unit||'');r=r.replace(/{action}/g,d.action||'赠送'); return r.trim();}

    // --- 语音播报 & 队列 (unchanged from v1.5) ---
    function loadVoices(){voices=synth.getVoices().filter(v=>v.lang.startsWith('zh'));updateVoiceListUI();const sURI=settings.selectedVoice;if(sURI){const s=document.getElementById(SCRIPT_PREFIX+'voiceSelect');if(s){s.value=sURI;if(s.selectedIndex===-1&&voices.length>0){s.selectedIndex=0;settings.selectedVoice=s.value;saveSettings();}}}else if(voices.length>0){settings.selectedVoice=voices[0].voiceURI;saveSettings();const s=document.getElementById(SCRIPT_PREFIX+'voiceSelect');if(s)s.value=settings.selectedVoice;}}
    function queueSpeak(t){if(!settings.enabled||!t)return;ttsQueue.push(t);processTTSQueue();}
    function processTTSQueue(){if(!settings.enabled||isSpeaking||ttsQueue.length===0)return;if(settings.ttsEngine==='browser'){processTTSQueueBrowser();}else if(settings.ttsEngine==='external'){processTTSQueueExternal();}else{console.error("[Bili TTS] Invalid TTS Engine:",settings.ttsEngine);}}
    function processTTSQueueBrowser(){isSpeaking=true;const t=ttsQueue.shift();if(!t){isSpeaking=false;return;}if(voices.length===0&&!synth.getVoices().some(v=>v.default&&v.lang.startsWith('zh'))){console.warn("[Bili TTS] No Chinese voices.");isSpeaking=false;processTTSQueue();return;}const u=new SpeechSynthesisUtterance(t);const sURI=settings.selectedVoice;const sV=voices.find(v=>v.voiceURI===sURI);if(sV)u.voice=sV;else console.warn(`[Bili TTS] Voice not found: ${sURI}.`);u.rate=settings.speechRate;u.volume=settings.speechVolume;u.onend=()=>{isSpeaking=false;processTTSQueue();};u.onerror=(e)=>{console.error('[Bili TTS] Speech error:',e.error);isSpeaking=false;processTTSQueue();};try{synth.speak(u);}catch(e){console.error('[Bili TTS] synth.speak error:',e);isSpeaking=false;processTTSQueue();}}
    function processTTSQueueExternal(){isSpeaking=true;const t=ttsQueue.shift();if(!t){isSpeaking=false;return;}const urlT=settings.externalTtsUrlTemplate;if(!urlT||!urlT.includes('{encodedText}')){console.error("[Bili TTS] External URL invalid:",urlT);isSpeaking=false;processTTSQueue();return;}let url;try{url=urlT.replace('{encodedText}',encodeURIComponent(t));}catch(e){console.error("[Bili TTS] URL encode error:",e);isSpeaking=false;processTTSQueue();return;}currentAudioElement=new Audio(url);currentAudioElement.volume=settings.speechVolume;try{currentAudioElement.playbackRate=settings.speechRate;}catch(e){}const onEnd=()=>{cleanupAudioElement();isSpeaking=false;processTTSQueue();};const onError=(e)=>{console.error('[Bili TTS] External TTS Audio error:',e);cleanupAudioElement();isSpeaking=false;processTTSQueue();};currentAudioElement.addEventListener('ended',onEnd,{once:true});currentAudioElement.addEventListener('error',onError,{once:true});currentAudioElement.play().catch(onError);}
    function cleanupAudioElement(){if(currentAudioElement){currentAudioElement.pause();currentAudioElement.removeAttribute('src');currentAudioElement.load();currentAudioElement=null;}}
    function stopAndClearTTS(){ttsQueue.length=0;if(synth.speaking)synth.cancel();cleanupAudioElement();isSpeaking=false;console.log('[Bili TTS] Speech stopped & queue cleared.');}

    // --- 整点报时 ---
    function scheduleNextChime() {
        if (hourlyChimeTimeoutId) {
            clearTimeout(hourlyChimeTimeoutId);
            hourlyChimeTimeoutId = null;
        }
        if (!settings.hourlyChimeEnabled) return;

        const now = new Date();
        const nextHour = new Date(now);
        nextHour.setHours(now.getHours() + 1);
        nextHour.setMinutes(0);
        nextHour.setSeconds(0);
        nextHour.setMilliseconds(0);

        const msUntilNextHour = nextHour.getTime() - now.getTime();

        // console.log(`[Bili TTS Chime] Scheduling next chime in ${msUntilNextHour} ms`);
        hourlyChimeTimeoutId = setTimeout(triggerHourlyChime, msUntilNextHour + 50); // Add small buffer
    }

    function triggerHourlyChime() {
        // Double check if still enabled when timeout triggers
        if (!settings.enabled || !settings.hourlyChimeEnabled) {
            scheduleNextChime(); // Reschedule (which will likely just return if disabled)
            return;
        }

        const now = new Date();
        // Final check to prevent duplicate calls if timeout fires slightly early/late
        if (now.getMinutes() !== 0 || now.getSeconds() > 1) { // Allow 0 or 1 second past
             scheduleNextChime(); // Reschedule immediately
             return;
        }

        const hour24 = now.getHours();
        let hour12 = hour24 % 12;
        if (hour12 === 0) hour12 = 12; // 0 should be 12 for 12-hour format
        const ampm = hour24 < 12 ? '上午' : '下午';

        const chimeData = {
            hour: hour24,
            hour12: hour12,
            ampm: ampm,
        };

        // Format using a specific chime template, similar to other templates
        let chimeText = settings.hourlyChimeTemplate || '';
        chimeText = chimeText.replace(/{hour}/g, chimeData.hour);
        chimeText = chimeText.replace(/{hour12}/g, chimeData.hour12);
        chimeText = chimeText.replace(/{ampm}/g, chimeData.ampm);
        chimeText = chimeText.trim();


        if (chimeText) {
            console.log(`[Bili TTS Speak Queue] ${chimeText} (Hourly Chime)`);
            queueSpeak(chimeText);
        }

        // Schedule the *next* hour's chime
        scheduleNextChime();
    }


    // --- UI 创建与管理 ---
    function createUI() {
        loadSettings();
        const btn=document.createElement('button');btn.id=SCRIPT_PREFIX+'toggleButton';btn.textContent='TTS设置';btn.style.cssText='position:fixed;bottom:60px;right:10px;z-index:9998;padding:5px 10px;cursor:pointer;';btn.onclick=toggleSettingsPanel;document.body.appendChild(btn);
        const pnl=document.createElement('div');pnl.id=SCRIPT_PREFIX+'settingsPanel';pnl.style.cssText='display:none;position:fixed;top:50%;left:50%;transform:translate(-50%, -50%);width:450px;max-height:85vh;overflow-y:auto;background-color:rgba(255, 255, 255, 0.98);border:1px solid #ccc;border-radius:8px;padding:20px;z-index:9999;box-shadow:0 4px 15px rgba(0,0,0,0.25);font-size:13px;color:#333;';
        const tb=document.createElement('div');tb.style.cssText='display:flex;justify-content:space-between;align-items:center;margin-bottom:20px;';const t=document.createElement('h3');t.textContent='Bili Live TTS 设置';t.style.margin='0';const cb=document.createElement('button');cb.textContent='×';cb.style.cssText='border:none;background:transparent;font-size:24px;cursor:pointer;line-height:1;';cb.onclick=toggleSettingsPanel;tb.appendChild(t);tb.appendChild(cb);pnl.appendChild(tb);

        const gf=document.createElement('fieldset');gf.style.borderColor='#ddd';const gl=document.createElement('legend');gl.textContent='全局设置';gf.appendChild(gl);
        gf.appendChild(createCheckbox(SCRIPT_PREFIX+'enabled','启用语音播报',settings.enabled,(e)=>{settings.enabled=e.target.checked;if(!settings.enabled)stopAndClearTTS();saveSettings(); scheduleNextChime(); /* Reschedule/clear chime */ })); // Also update chime schedule
        const engineContainer=document.createElement('div');engineContainer.className='input-field-container';engineContainer.style.marginBottom='10px';const engineLabel=document.createElement('label');engineLabel.textContent='TTS引擎: ';engineContainer.appendChild(engineLabel);engineContainer.appendChild(createRadioGroup(SCRIPT_PREFIX+'ttsEngine',[{label:'浏览器',value:'browser'},{label:'第三方API',value:'external'}],settings.ttsEngine,(v)=>{settings.ttsEngine=v;saveSettings();toggleExternalTtsUrlInput(v==='external');stopAndClearTTS();}));gf.appendChild(engineContainer);
        const externalUrlDiv=createInputField(SCRIPT_PREFIX+'externalTtsUrlTemplate','API URL模板',settings.externalTtsUrlTemplate,'textarea',(v)=>{settings.externalTtsUrlTemplate=v;saveSettings();},'例: https://service.com/tts?text={encodedText}');externalUrlDiv.id=SCRIPT_PREFIX+'externalTtsUrlDiv';externalUrlDiv.style.display=settings.ttsEngine==='external'?'flex':'none';gf.appendChild(externalUrlDiv); const externalUrlHelp=document.createElement('div');externalUrlHelp.id=SCRIPT_PREFIX+'externalTtsUrlHelp';externalUrlHelp.style.cssText='font-size:11px; color:#666; margin-left: 150px; margin-top:-5px; margin-bottom: 8px; display:'+(settings.ttsEngine==='external'?'block':'none');externalUrlHelp.textContent='必须包含 {encodedText} 占位符。';gf.appendChild(externalUrlHelp);
        const voiceDiv=createInputField(SCRIPT_PREFIX+'voiceSelect','选择语音',settings.selectedVoice,'select',(v)=>{settings.selectedVoice=v;saveSettings();queueSpeak("测试语音");},'',null,null,'auto');voiceDiv.id=SCRIPT_PREFIX+'browserVoiceDiv';voiceDiv.style.display=settings.ttsEngine==='browser'?'flex':'none';gf.appendChild(voiceDiv);
        gf.appendChild(createRangeInput(SCRIPT_PREFIX+'speechRate','语速',settings.speechRate,0.5,2,0.1,(v)=>{settings.speechRate=v;saveSettings();queueSpeak(`语速${v.toFixed(1)}`);}));
        gf.appendChild(createRangeInput(SCRIPT_PREFIX+'speechVolume','音量',settings.speechVolume,0,1,0.1,(v)=>{settings.speechVolume=v;saveSettings();}));
        gf.appendChild(createInputField(SCRIPT_PREFIX+'globalBlockUserIds','屏蔽用户ID(逗号/换行)',settings.globalBlockUserIds,'textarea',(v)=>{settings.globalBlockUserIds=v;saveSettings();},'例: 123\\n456,789'));
        gf.appendChild(createInputField(SCRIPT_PREFIX+'globalBlockKeywords','屏蔽用户名关键词(逗号/换行)',settings.globalBlockKeywords,'textarea',(v)=>{settings.globalBlockKeywords=v;saveSettings();},'例: 机器人\\n测试'));

        // --- Hourly Chime Settings ---
        gf.appendChild(createCheckbox(SCRIPT_PREFIX+'hourlyChimeEnabled','启用整点报时',settings.hourlyChimeEnabled,(e)=>{settings.hourlyChimeEnabled=e.target.checked;saveSettings(); scheduleNextChime(); /* Update schedule */}));
        gf.appendChild(createInputField(SCRIPT_PREFIX+'hourlyChimeTemplate','报时模板',settings.hourlyChimeTemplate,'text',(v)=>{settings.hourlyChimeTemplate=v;saveSettings();}));

        pnl.appendChild(gf);

        const ff=document.createElement('fieldset');ff.style.borderColor='#ddd';const fl=document.createElement('legend');fl.textContent='分类过滤与模板';ff.appendChild(fl);
        ff.appendChild(createFilterSection('danmu','弹幕',[ {id:'contentKeywords',label:'内容白名单(包含则播)',type:'textarea',placeholder:'逗号/换行,留空不过滤'}, {id:'contentKeywordsBlock',label:'内容黑名单(包含不播)',type:'textarea',placeholder:'逗号/换行'}, {id:'hasMedal',label:'需要粉丝牌',type:'checkbox'},{id:'minMedalLevel',label:'最低粉丝牌等级',type:'number',min:0,step:1}, {id:'danmuDebounceEnabled',label:'启用弹幕去重',type:'checkbox'}, {id:'danmuDebounceTime',label:'弹幕去重时间(秒)',type:'number',min:0,step:1,placeholder:'30'} ],settings.templates.danmu,(v)=>{settings.templates.danmu=v;saveSettings();}));
        ff.appendChild(createFilterSection('gift','礼物',[ {id:'minPrice',label:'最低价值(元)',type:'number',min:0,step:0.1},{id:'hasMedal',label:'需要粉丝牌',type:'checkbox'},{id:'minMedalLevel',label:'最低粉丝牌等级',type:'number',min:0,step:1} ],settings.templates.gift,(v)=>{settings.templates.gift=v;saveSettings();}));
        ff.appendChild(createFilterSection('superchat','SC',[ {id:'minPrice',label:'最低价值(元)',type:'number',min:0,step:1},{id:'hasMedal',label:'需要粉丝牌',type:'checkbox'},{id:'minMedalLevel',label:'最低粉丝牌等级',type:'number',min:0,step:1} ],settings.templates.superchat,(v)=>{settings.templates.superchat=v;saveSettings();}));
        ff.appendChild(createFilterSection('guard','上舰',[ {id:'level3',label:'播报舰长',type:'checkbox'},{id:'level2',label:'播报提督',type:'checkbox'},{id:'level1',label:'播报总督',type:'checkbox'} ],settings.templates.guard,(v)=>{settings.templates.guard=v;saveSettings();}));
        ff.appendChild(createFilterSection('interact','互动',[ {id:'typeEnter',label:'播报入场',type:'checkbox'},{id:'typeFollow',label:'播报关注',type:'checkbox'},{id:'typeShare',label:'播报分享',type:'checkbox'},{id:'hasMedal',label:'需要粉丝牌',type:'checkbox'},{id:'minMedalLevel',label:'最低粉丝牌等级',type:'number',min:0,step:1} ],settings.templates.interact,(v)=>{settings.templates.interact=v;saveSettings();}));
        pnl.appendChild(ff);

        const th=document.createElement('div');th.style.cssText='margin-top:15px;font-size:11px;color:#666;line-height:1.4;';th.innerHTML=`<b>内容模板占位符:</b> {username},{uid},{text},{giftName},{count},{price},{levelName},{actionText},{medalLevel},{num},{unit},{action}<br/><b>报时模板占位符:</b> {hour}(0-23), {hour12}(1-12), {ampm}(上午/下午)`;pnl.appendChild(th);
        document.body.appendChild(pnl);

        loadVoices();if(synth.onvoiceschanged!==undefined)synth.onvoiceschanged=loadVoices;updateVoiceListUI();
        scheduleNextChime(); // Initial schedule for chime
    }

    // --- UI Helper Functions (unchanged from v1.5 except slight adjustments) ---
    function createFilterSection(cat,tit,fields,tplVal,onTplChg){const s=document.createElement('div');s.style.cssText='margin-bottom:10px;padding:10px;border:1px solid #eee;border-radius:4px;';s.appendChild(createCheckbox(SCRIPT_PREFIX+cat+'_enabled',`播报 ${tit}`,settings.filters[cat].enabled,(e)=>{settings.filters[cat].enabled=e.target.checked;saveSettings();const d=s.querySelector(`.${SCRIPT_PREFIX}details`);if(d)d.style.display=e.target.checked?'block':'none';})); const d=document.createElement('div');d.className=SCRIPT_PREFIX+'details';d.style.cssText='margin-top:10px;padding-left:15px;border-left:2px solid #eee;display:'+(settings.filters[cat].enabled?'block':'none')+';'; fields.forEach(f=>{const val=settings.filters[cat][f.id];const defaultVal=(f.type==='number'?(f.min??0):'');if(f.type==='checkbox')d.appendChild(createCheckbox(SCRIPT_PREFIX+cat+'_'+f.id,f.label,val,(e)=>{settings.filters[cat][f.id]=e.target.checked;saveSettings();})); else d.appendChild(createInputField(SCRIPT_PREFIX+cat+'_'+f.id,f.label,val??defaultVal,f.type,(v)=>{settings.filters[cat][f.id]=v;saveSettings();},f.placeholder||'',f.min,f.step));}); d.appendChild(createInputField(SCRIPT_PREFIX+cat+'_template','播报模板',tplVal,'text',onTplChg,'',null,null,'95%')); s.appendChild(d);return s;}
    function createInputField(id,lblTxt,val,type,onChg,ph='',min=null,step=null,w='auto'){const d=document.createElement('div');d.className='input-field-container';d.style.marginBottom='8px';const l=document.createElement('label');l.htmlFor=id;l.textContent=lblTxt+': ';let i;if(type==='textarea'){i=document.createElement('textarea');i.id=id;i.value=val;i.placeholder=ph;i.rows=2;i.style.width='95%';i.style.resize='vertical';i.oninput=(e)=>onChg(e.target.value);}else if(type==='select'){i=document.createElement('select');i.id=id;i.style.maxWidth='220px';i.onchange=(e)=>onChg(e.target.value);i.value=val;}else{i=document.createElement('input');i.type=type;i.id=id;i.value=val;i.placeholder=ph;i.style.width=w;if(type==='number'){if(min!==null)i.min=min;if(step!==null)i.step=step;i.style.width='70px';} i.oninput=(e)=>{let v=e.target.value;if(type==='number'){v=parseFloat(v);if(isNaN(v))v=min!==null?min:0;}onChg(v);};} d.appendChild(l);d.appendChild(i);return d;}
    function createRangeInput(id,lblTxt,val,min,max,step,onChg){const d=document.createElement('div');d.className='input-field-container range-container';d.style.marginBottom='8px';const l=document.createElement('label');l.htmlFor=id;l.textContent=lblTxt+': ';const i=document.createElement('input');i.type='range';i.id=id;i.min=min;i.max=max;i.step=step;i.value=val;i.style.cssText='flex-grow:1;margin:0 5px;cursor:pointer;vertical-align:middle;';const s=document.createElement('span');const p=step.toString().includes('.')?step.toString().split('.')[1].length:0;s.textContent=parseFloat(val).toFixed(p);s.style.cssText='min-width:35px;text-align:right;font-size:12px;color:#555;vertical-align:middle;';i.oninput=(e)=>{const v=parseFloat(e.target.value);s.textContent=v.toFixed(p);onChg(v);};d.appendChild(l);d.appendChild(i);d.appendChild(s);return d;}
    function createCheckbox(id,lblTxt,chk,onChg){const d=document.createElement('div');d.style.marginBottom='8px';const i=document.createElement('input');i.type='checkbox';i.id=id;i.checked=chk;i.onchange=onChg;i.style.cssText='margin-right:5px;vertical-align:middle;';const l=document.createElement('label');l.htmlFor=id;l.textContent=lblTxt;l.style.cssText='cursor:pointer;vertical-align:middle;';d.appendChild(i);d.appendChild(l);return d;}
    function createRadioGroup(name,opts,curVal,onChg){const c=document.createElement('div');c.style.display='inline-block';opts.forEach(o=>{const id=SCRIPT_PREFIX+name+'_'+o.value;const r=document.createElement('input');r.type='radio';r.id=id;r.name=name;r.value=o.value;r.checked=o.value===curVal;r.style.cssText='margin:0 5px 0 10px;vertical-align:middle;';r.onchange=(e)=>{if(e.target.checked)onChg(o.value);};const l=document.createElement('label');l.htmlFor=id;l.textContent=o.label;l.style.cssText='cursor:pointer;vertical-align:middle;';c.appendChild(r);c.appendChild(l);});return c;}
    function toggleExternalTtsUrlInput(show){const u=document.getElementById(SCRIPT_PREFIX+'externalTtsUrlDiv');const h=document.getElementById(SCRIPT_PREFIX+'externalTtsUrlHelp');const b=document.getElementById(SCRIPT_PREFIX+'browserVoiceDiv');if(u)u.style.display=show?'flex':'none';if(h)h.style.display=show?'block':'none';if(b)b.style.display=show?'none':'flex';}
    function updateVoiceListUI(){const s=document.getElementById(SCRIPT_PREFIX+'voiceSelect');if(!s||s.tagName!=='SELECT')return;const c=s.value;s.innerHTML='';if(voices.length===0){const o=document.createElement('option');o.textContent='无可用中文语音';o.disabled=true;s.appendChild(o);}else{voices.forEach(v=>{const o=document.createElement('option');o.value=v.voiceURI;o.textContent=`${v.name} (${v.lang})`;if(v.voiceURI===settings.selectedVoice)o.selected=true;s.appendChild(o);}); if(settings.selectedVoice&&voices.some(v=>v.voiceURI===settings.selectedVoice))s.value=settings.selectedVoice; else if(voices.length>0){s.selectedIndex=0;settings.selectedVoice=s.value;saveSettings();}}}
    function toggleSettingsPanel(){const p=document.getElementById(SCRIPT_PREFIX+'settingsPanel');if(p)p.style.display=p.style.display==='none'?'block':'none';}

    // --- Settings Persistence (unchanged from v1.5) ---
    function saveSettings(){try{GM_setValue(SCRIPT_PREFIX+'settings',JSON.stringify(settings));}catch(e){console.error('[Bili TTS] Save Err:',e);}}
    function loadSettings(){try{const s=GM_getValue(SCRIPT_PREFIX+'settings',null);if(s)settings=mergeDeep(JSON.parse(JSON.stringify(DEFAULT_SETTINGS)),JSON.parse(s));else settings=JSON.parse(JSON.stringify(DEFAULT_SETTINGS));/*console.log('[Bili TTS] Settings loaded/defaulted.');*/}catch(e){console.error('[Bili TTS] Load Err:',e);settings=JSON.parse(JSON.stringify(DEFAULT_SETTINGS));}}
    function mergeDeep(t,s){const o=Object.assign({},t);if(isObject(t)&&isObject(s)){Object.keys(s).forEach(k=>{if(isObject(s[k])){if(!(k in t)||!isObject(t[k]))Object.assign(o,{[k]:s[k]});else o[k]=mergeDeep(t[k],s[k]);}else{if(s[k]!==undefined&&s[k]!==null)Object.assign(o,{[k]:s[k]});else if(!(k in t)||t[k]===undefined||t[k]===null)Object.assign(o,{[k]:s[k]});}}); }return o;}
    function isObject(i){return(i&&typeof i==='object'&&!Array.isArray(i));}

    // --- Initialization ---
    GM_addStyle(`
        #${SCRIPT_PREFIX}settingsPanel input[type="text"], #${SCRIPT_PREFIX}settingsPanel input[type="number"], #${SCRIPT_PREFIX}settingsPanel select, #${SCRIPT_PREFIX}settingsPanel textarea { padding: 5px; border: 1px solid #ccc; border-radius: 3px; margin-left: 5px; vertical-align: middle; box-sizing: border-box; font-size:12px; background-color: #fff; color: #333; }
        #${SCRIPT_PREFIX}settingsPanel textarea { line-height: 1.4; min-height: 40px; }
        #${SCRIPT_PREFIX}settingsPanel fieldset { border: 1px solid #ddd; border-radius: 4px; padding: 10px 15px; margin-bottom: 15px; background-color: #fdfdfd; }
        #${SCRIPT_PREFIX}settingsPanel legend { font-weight: bold; color: #555; padding: 0 5px; }
        #${SCRIPT_PREFIX}toggleButton { background-color:#00a1d6;color:white;border:none;border-radius:4px;box-shadow:0 1px 3px rgba(0,0,0,0.2);transition:background-color .2s;font-size:12px;padding:5px 10px; } #${SCRIPT_PREFIX}toggleButton:hover { background-color:#00b5e5; }
        .${SCRIPT_PREFIX}details { margin-top: 10px; padding-left: 15px; border-left: 2px solid #eee; }
        #${SCRIPT_PREFIX}settingsPanel { scrollbar-width: thin; scrollbar-color: #aaa #eee; }
        #${SCRIPT_PREFIX}settingsPanel::-webkit-scrollbar { width: 8px; } #${SCRIPT_PREFIX}settingsPanel::-webkit-scrollbar-track { background: #eee; border-radius: 4px; } #${SCRIPT_PREFIX}settingsPanel::-webkit-scrollbar-thumb { background-color: #aaa; border-radius: 4px; border: 2px solid #eee; }
        .input-field-container { display: flex; align-items: flex-start; flex-wrap: nowrap; margin-bottom: 8px; }
        .input-field-container label { flex-basis: 140px; flex-shrink: 0; text-align: right; margin-right: 8px; color: #444; padding-top: 5px; line-height: 1.4; }
        .input-field-container input, .input-field-container select, .input-field-container textarea { flex-grow: 1; min-width: 100px; }
        .input-field-container.range-container label { padding-top: 2px; }
        .input-field-container.range-container input[type="range"] { margin-top: 0; vertical-align: middle;}
        .input-field-container.range-container span { vertical-align: middle; }
        .input-field-container input[type="radio"] + label { cursor: pointer; }
    `);

    const observer=new MutationObserver((m,o)=>{if(document.body){createUI();o.disconnect();}}); if(document.body)createUI(); else observer.observe(document.documentElement||document,{childList:true,subtree:true});
    console.log('[Bili TTS] Script v1.6 Loaded.');

})();
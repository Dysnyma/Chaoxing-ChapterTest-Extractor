// ==UserScript==
// @name         学习通章节测验提取器
// @namespace    https://github.com/chaoxing-test-extractor
// @version      1.1.0
// @description  自动提取学习通课程所有章节测验的题目和答案，支持字体解密、TXT/JSON导出
// @author       CKC
// @match        *://mooc2-ans.chaoxing.com/mooc2-ans/mycourse/stu*
// @match        *://mooc1.chaoxing.com/mooc-ans/knowledge/cards*
// @match        *://mooc1.chaoxing.com/mooc-ans/work/selectWorkQuestion*
// @match        *://mooc1.chaoxing.com/mycourse/studentstudy*
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_xmlhttpRequest
// @connect      mooc1.chaoxing.com
// @connect      mooc2-ans.chaoxing.com
// @run-at       document-end
// ==/UserScript==

(function () {
  'use strict';

  const CONF = {
    delayCh: { min: 2500, max: 4500 },
    delayCard: { min: 1000, max: 2000 },
    iframeTimeout: 18000,
    maxCards: 20,
    panelWidth: 380,
    debug: true,  // 开启调试日志，排查问题时查看浏览器控制台(F12)
  };

  function log(...a) { if (CONF.debug) console.log('[CX提取]', ...a); }
  function sleep(ms) { return new Promise(r => setTimeout(r, ms)); }
  function randDelay(cfg) { return sleep(cfg.min + Math.random() * (cfg.max - cfg.min)); }

  // ===================== 状态 =====================
  const S = {
    running: false, stopped: false,
    courseInfo: null,
    chapters: [],
    results: [],           // [{chapterName, questions:[{type,stem,options:[{label,text}],answer,analysis}]}]
    curChIdx: -1, totalCh: 0, doneCh: 0, totalQ: 0,
  };

  // ===================== 字体解密（Canvas字形对比法） =====================
  const FontDec = {
    _cache: {},
    _ref: null,

    detect(doc) {
      const fonts = [];
      try {
        for (const sheet of doc.styleSheets) {
          try {
            for (const rule of sheet.cssRules || []) {
              if (rule instanceof CSSFontFaceRule &&
                rule.style.getPropertyValue('font-family').includes('font-cxsecret')) {
                const src = rule.style.getPropertyValue('src');
                const m = src.match(/base64,([^'")]+)/);
                if (m) fonts.push({ family: rule.style.getPropertyValue('font-family').trim(), b64: m[1] });
              }
            }
          } catch (e) { /* cross-origin */ }
        }
      } catch (e) { /* ignore */ }
      return fonts;
    },

    _b64ToBytes(b64) {
      const bin = atob(b64.replace(/\s/g, ''));
      const arr = new Uint8Array(bin.length);
      for (let i = 0; i < bin.length; i++) arr[i] = bin.charCodeAt(i);
      return arr;
    },

    parseCmap(fnt) {
      const d = new DataView(fnt.buffer, fnt.byteOffset, fnt.byteLength);
      const r16 = o => d.getUint16(o, false);
      const r32 = o => d.getUint32(o, false);
      const numTables = r16(4);
      let off = null;
      for (let i = 0; i < numTables; i++) {
        const tag = String.fromCharCode(d.getUint8(12 + i * 16), d.getUint8(13 + i * 16), d.getUint8(14 + i * 16), d.getUint8(15 + i * 16));
        if (tag === 'cmap') { off = r32(12 + i * 16 + 8); break; }
      }
      if (off === null) return [];
      const pts = new Set();
      const n = r16(off + 2);
      for (let i = 0, to = off + 4; i < n; i++, to += 8) {
        const plat = r16(to), enc = r16(to + 2), sub = off + r32(to + 4);
        if (plat !== 0 && plat !== 3) continue;
        const fmt = r16(sub);
        if (fmt === 4) {
          const sc = r16(sub + 6) / 2, ec = sub + 14, st = ec + 2 + sc * 2, dd = st + sc * 2, ro = dd + sc * 2;
          for (let s = 0; s < sc; s++) {
            const start = r16(st + s * 2), end = r16(ec + s * 2), delta = r16(dd + s * 2), rg = r16(ro + s * 2);
            for (let c = start; c <= end; c++) {
              let g; if (rg !== 0) { const oo = ro + s * 2 + rg + (c - start) * 2; g = r16(oo); if (g !== 0) g = (g + delta) & 0xFFFF; }
              else g = (c + delta) & 0xFFFF;
              if (g !== 0) pts.add(c);
            }
          }
        } else if (fmt === 6) {
          const f = r16(sub + 6), c = r16(sub + 8);
          for (let x = f; x < f + c; x++) pts.add(x);
        } else if (fmt === 12 || fmt === 13) {
          const ng = r32(sub + 12);
          for (let g = 0; g < ng; g++) {
            const start = r32(sub + 16 + g * 12), end = r32(sub + 20 + g * 12);
            for (let x = start; x <= end; x++) pts.add(x);
          }
        }
      }
      return [...pts];
    },

    collectObserved(doc, family) {
      const seen = new Set();
      const fl = family.toLowerCase();
      const all = doc.querySelectorAll('*');
      for (const el of all) {
        try {
          const s = doc.defaultView.getComputedStyle(el);
          if (s.fontFamily && s.fontFamily.toLowerCase().includes(fl))
            for (const ch of el.textContent || '') seen.add(ch);
        } catch (e) { /* ignore */ }
      }
      return [...seen].slice(0, 500);
    },

    render(ch, font, sz) {
      const c = document.createElement('canvas');
      c.width = c.height = sz;
      const ctx = c.getContext('2d');
      ctx.fillStyle = '#000'; ctx.fillRect(0, 0, sz, sz);
      ctx.fillStyle = '#fff';
      ctx.font = `${sz * 0.8}px "${font}", sans-serif`;
      ctx.textBaseline = 'middle'; ctx.textAlign = 'center';
      ctx.fillText(ch, sz / 2, sz / 2);
      return ctx.getImageData(0, 0, sz, sz);
    },

    _hash(img) {
      let ink = 0, n = 0;
      for (let i = 0; i < img.data.length; i += 4) { n++; if (img.data[i] > 128) ink++; }
      return { ink, n };
    },

    _cmp(a, b) {
      let d = 0;
      for (let i = 0; i < a.data.length; i += 4) d += (a.data[i] > 128 ? 1 : 0) !== (b.data[i] > 128 ? 1 : 0) ? 1 : 0;
      return d;
    },

    decode(obs, sf) {
      const cand = [];
      for (let cp = 0x4E00; cp <= 0x9FFF; cp++) cand.push(String.fromCodePoint(cp));
      for (let cp = 0x30; cp <= 0x39; cp++) cand.push(String.fromCodePoint(cp));
      for (let cp = 0x41; cp <= 0x5A; cp++) cand.push(String.fromCodePoint(cp));
      for (let cp = 0x61; cp <= 0x7A; cp++) cand.push(String.fromCodePoint(cp));

      const sz = 32, map = {};
      const chash = {};
      for (const ch of cand) chash[ch] = this._hash(this.render(ch, 'sans-serif', sz));

      for (const o of obs) {
        const oimg = this.render(o, sf, sz);
        const oh = this._hash(oimg);
        if (!oh) continue;
        let best = null, bestD = Infinity;
        for (const [c, ch] of Object.entries(chash)) {
          if (!ch) continue;
          if (Math.abs(oh.ink - ch.ink) > oh.n * 0.2) continue;
          const ci = this.render(c, 'sans-serif', sz);
          const diff = this._cmp(oimg, ci);
          if (diff < bestD) { bestD = diff; best = c; }
        }
        if (best && bestD < oh.n * 0.3) map[o] = best;
      }
      return map;
    },

    forDoc(doc) {
      const fonts = this.detect(doc);
      const all = {};
      for (const f of fonts) {
        const obs = this.collectObserved(doc, f.family);
        if (obs.length > 0) Object.assign(all, this.decode(obs, f.family));
      }
      return all;
    },

    apply(text, map) {
      let r = '';
      for (const ch of text) r += map[ch] || ch;
      return r;
    },
  };

  // ===================== mArg 数据解析（知识卡片页面的核心数据源） =====================
  function parseMArg(doc) {
    const scripts = doc.querySelectorAll('script');
    for (const s of scripts) {
      const text = s.textContent || s.innerText || '';
      const m = text.match(/mArg\s*=\s*(\{[\s\S]*?\})\s*\}\s*catch/i);
      if (m) {
        try {
          return JSON.parse(m[1]);
        } catch (e) {
          log('mArg JSON解析失败:', e.message);
        }
      }
    }
    return null;
  }

  // 从 mArg 中提取题目数据
  function extractFromMArg(mArg, fontMap) {
    const questions = [];
    try {
      // 遍历 attachments/questions
      const attachments = mArg?.attachments || [];
      for (const att of attachments) {
        if (att?.job === true && att?.property?._jobid) {
          // 这是一个任务点
          const qArr = att?.property?.questions || att?.property?.data || [];
          for (const q of qArr) {
            const parsed = parseMArgQuestion(q);
            if (parsed) {
              parsed.stem = FontDec.apply(parsed.stem, fontMap);
              parsed.options = parsed.options.map(o =>
                ({ label: o.label, text: FontDec.apply(o.text, fontMap) }));
              parsed.answer = FontDec.apply(parsed.answer, fontMap);
              parsed.analysis = FontDec.apply(parsed.analysis, fontMap);
              questions.push(parsed);
            }
          }
        }
      }
    } catch (e) {
      log('从mArg提取题目失败:', e.message);
    }
    return questions;
  }

  function parseMArgQuestion(q) {
    if (!q?.description) return null;

    let stem = (q.description || '').replace(/<[^>]+>/g, '').trim();
    if (!stem || stem.length < 2) return null;

    // 题型映射
    const typeMap = {
      '0': '单选题', 'singlechoice': '单选题', 'single': '单选题', 'radio': '单选题',
      '1': '多选题', 'multiplechoice': '多选题', 'multiple': '多选题', 'checkbox': '多选题',
      '2': '填空题', 'fillblank': '填空题', 'fill': '填空题', 'blank': '填空题',
      '3': '判断题', 'judgement': '判断题', 'judge': '判断题', 'tf': '判断题',
      '4': '简答题', 'shortanswer': '简答题', 'short': '简答题',
    };
    const type = typeMap[(q.type || '').toString().toLowerCase()] || typeMap[q.questionType] || '单选题';

    // 选项
    const options = [];
    const optSource = q.options || q.choices || q.optionList || q.answerList || [];
    const labels = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
    for (let i = 0; i < optSource.length; i++) {
      const opt = optSource[i];
      const text = typeof opt === 'string' ? opt : (opt?.content || opt?.text || opt?.optionContent || opt?.name || '');
      const label = opt?.label || opt?.key || labels[i];
      if (text) options.push({ label, text: String(text).replace(/<[^>]+>/g, '').trim() });
    }

    // 答案
    let answer = q.answer || q.correctAnswer || q.rightAnswer || q.key || '';
    if (Array.isArray(answer)) answer = answer.join(', ');
    if (typeof answer === 'object') answer = JSON.stringify(answer);
    answer = String(answer).replace(/<[^>]+>/g, '').trim();

    // 解析
    let analysis = q.analysis || q.explain || q.explanation || q.solution || '';
    analysis = String(analysis).replace(/<[^>]+>/g, '').trim();

    // 题目ID（防重复唯一标识）
    const qid = q.id || q.questionId || q.itemId || '';
    if (qid) stem = `[${qid}] ${stem}`;

    return { type, stem, options, answer, analysis };
  }

  // ===================== 课程信息 =====================
  function getCourseInfo() {
    const url = location.href;
    const getParam = (name) => {
      const m = url.match(new RegExp('[?&]' + name + '=([^&]+)'));
      return m ? decodeURIComponent(m[1]) : '';
    };
    const getVal = (id) => document.getElementById(id)?.value || '';

    const ci = {
      courseId: getVal('courseid') || getParam('courseid') || getParam('courseId'),
      clazzId: getVal('clazzid') || getParam('clazzid') || getParam('clazzId'),
      cpi: getVal('cpi') || getParam('cpi'),
      enc: getVal('enc') || getParam('enc'),
      oldenc: getVal('oldenc') || getParam('oldenc') || getVal('enc') || getParam('enc'),
      name: '',
    };

    // 尝试多种方式获取课程名
    const titleEl = document.querySelector('.classDl dd');
    if (titleEl) { ci.name = titleEl.textContent.trim(); }
    if (!ci.name) {
      // studentstudy 页面可能有 .prev_title
      const prevT = document.querySelector('.prev_title');
      if (prevT) { ci.name = prevT.textContent.trim(); }
    }
    if (!ci.name) {
      // 从页面标题获取
      const t = document.title || '';
      ci.name = t.replace(/学生学习页面|章节|测试|测验/g, '').trim() || '未知课程';
    }
    return ci;
  }

  // 测试/测验相关的关键词（用于DOM匹配 — title属性包含匹配）
  const DEFAULT_KEYWORDS = ['单元测试', '单元测验', '章节测验', '章节测试', '课后测验', '课后测试', '本章测验', '章测试', '章测验'];

  function getKeywords() {
    try {
      const saved = GM_getValue('cx_keywords', null);
      if (saved && Array.isArray(saved)) return saved;
    } catch(e) {}
    return [...DEFAULT_KEYWORDS];
  }

  function saveKeywords(list) {
    GM_setValue('cx_keywords', list);
  }

  // ===================== 章节发现 =====================
  async function discoverChapters(ci) {
    log('开始章节发现... courseId=' + ci.courseId + ' clazzId=' + ci.clazzId);

    // 策略1: 从 studentcourse iframe 读取DOM（多重ID匹配）
    const iframeIds = ['frame_content-zj', 'frame_content', 'contentFrame'];
    let iframeDoc = null;
    for (const id of iframeIds) {
      const iframe = document.getElementById(id);
      if (iframe) {
        try {
          const doc = iframe.contentDocument || iframe.contentWindow.document;
          if (doc?.body && doc.body.children.length > 0) {
            iframeDoc = doc;
            log(`[iframe] 成功访问 iframe#${id}`);
            break;
          }
        } catch (e) { log(`[iframe] #${id} 无法访问:`, e.message); }
      }
    }

    if (iframeDoc) {
      const chs = parseChaptersFromDOM(iframeDoc, ci);
      if (chs.length > 0) { log(`[策略1-iframe] 发现 ${chs.length} 个章节`); return chs; }
      log('[策略1-iframe] DOM解析未发现章节，继续下一策略...');
    } else {
      log('[策略1-iframe] 未找到可访问的iframe');
    }

    // 策略2: fetch studentcourse 页面
    try {
      const html = await fetchPage(`/mooc2-ans/mycourse/studentcourse?courseid=${ci.courseId}&clazzid=${ci.clazzId}&cpi=${ci.cpi}&ut=s`);
      if (html && html.length > 500) {
        const doc = new DOMParser().parseFromString(html, 'text/html');
        const chs = parseChaptersFromDOM(doc, ci);
        if (chs.length > 0) { log(`[策略2-fetch] 发现 ${chs.length} 个章节`); return chs; }
        log('[策略2-fetch] DOM解析未发现章节');
      } else {
        log('[策略2-fetch] 响应内容太短，可能需要登录验证');
      }
    } catch (e) { log('[策略2-fetch] 失败:', e.message); }

    // 策略3: 尝试从当前主页面直接搜索章节元素（有些页面章节列表直接在主页面渲染）
    const mainChs = parseChaptersFromDOM(document, ci);
    if (mainChs.length > 0) { log(`[策略2b-主页DOM] 发现 ${mainChs.length} 个章节`); return mainChs; }

    // 策略4: 扫描页面所有脚本
    try {
      const chs = discoverFromScripts(ci);
      if (chs.length > 0) { log(`[策略3-script] 发现 ${chs.length} 个章节`); return chs; }
    } catch (e) { log('[策略3-script] 失败:', e.message); }

    // 策略5: 尝试通过 transfer API 获取课程结构
    try {
      const html = await fetchPage(`https://mooc1.chaoxing.com/mycourse/transfer?moocId=${ci.courseId}&clazzid=${ci.clazzId}&ut=s&refer=${encodeURIComponent(location.href)}`);
      if (html && html.length > 500) {
        const doc = new DOMParser().parseFromString(html, 'text/html');
        const chs = parseChaptersFromDOM(doc, ci);
        if (chs.length > 0) { log(`[策略4-transfer] 发现 ${chs.length} 个章节`); return chs; }
      }
    } catch (e) { log('[策略4-transfer] 失败:', e.message); }

    // 把发现的章节数和详情输出到状态
    const chSummary = chapters.map(c => c.name + ' [' + c.chapterId + ']').join(', ');
    log('最终章节列表(' + chapters.length + '):', chSummary);
    throw new Error('未能自动发现章节列表。\n\n可能原因：\n1. 请在课程主页运行脚本\n2. 确保页面已完全加载\n3. 尝试刷新页面后重试\n\n如持续失败，可尝试：打开任意章节测试页面，脚本将自动提取当前章节内容');
  }

  function fetchPage(url) {
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        method: 'GET', url,
        onload: r => resolve(r.responseText),
        onerror: e => reject(e),
        ontimeout: () => reject(new Error('timeout')),
        timeout: 15000,
      });
    });
  }

  // 检查 title 属性是否匹配测试关键词
  function isTestTitle(title) {
    const t = (title || '').trim();
    if (!t) return false;
    const keywords = getKeywords();
    return keywords.some(kw => t.includes(kw));
  }

  // DOM解析章节 — studentcourse 页面真实结构
  // <div class="chapter_item" id="cur1032809677" onclick="toOld('courseId','knowledgeId','clazzId',0)" title="单元测试">
  function parseChaptersFromDOM(doc, ci) {
    const chapters = [];
    const seen = new Set();

    // 方法A: 查找 .chapter_item[title] 元素（title="单元测试"）
    const testItems = doc.querySelectorAll('.chapter_item[title]');
    for (const item of testItems) {
      const title = (item.getAttribute('title') || '').trim();
      if (!isTestTitle(title)) continue;

      // 提取 knowledgeId
      let kid = '';
      // 从 id="cur1032809677" 提取
      const rawId = item.id || '';
      kid = rawId.replace(/^cur/, '');

      // 从 onclick="toOld('cid','kid','clid',0)" 提取（更准确）
      const onclick = item.getAttribute('onclick') || '';
      const onclickM = onclick.match(/toOld\s*\([^,]+,\s*['"](\d+)['"]/);
      if (onclickM) kid = onclickM[1];

      if (!kid) continue;

      // 查找所属的上级章节标题
      let chapterName = title; // 默认用测试名
      // 往上找 .chapter_unit 容器
      const unit = item.closest('.chapter_unit');
      if (unit) {
        // 在 .chapter_unit 内找第一级 .chapter_item > .chapter_Thats_bnt > .catalog_name span[title]
        const firstItem = unit.querySelector(':scope > .chapter_item');
        if (firstItem) {
          const titleSpan = firstItem.querySelector('.chapter_Thats_bnt .catalog_name span[title], .chapter_Thats_bnt span[title]');
          if (titleSpan) {
            chapterName = titleSpan.getAttribute('title') || titleSpan.textContent.trim();
          } else {
            // 回退：取第一个 chapter_item 的文本
            const firstNameSpan = firstItem.querySelector('.catalog_name span');
            if (firstNameSpan) chapterName = firstNameSpan.textContent.trim();
          }
        }
      }

      const key = kid;
      if (seen.has(key)) continue;
      seen.add(key);

      chapters.push({
        name: `${chapterName} - ${title}`,
        chapterId: kid,
        knowledgeIds: [kid],
      });

      log(`发现测试: ${chapterName} → ${title} [${kid}]`);
    }

    // 方法B: 如果没找到测试项，查找 onclick="toOld" 且 title 匹配的
    if (chapters.length === 0) {
      const items = doc.querySelectorAll('.chapter_item[onclick]');
      for (const item of items) {
        const onclick = item.getAttribute('onclick') || '';
        const onclickM = onclick.match(/toOld\s*\([^,]+,\s*['"](\d+)['"]/);
        if (!onclickM) continue;
        const kid = onclickM[1];

        // 检查 title 或文本是否匹配测试关键词
        const itemTitle = (item.getAttribute('title') || '').trim();
        const itemText = item.textContent.trim();

        if (!isTestTitle(itemTitle) && !TEST_KEYWORDS.some(kw => itemText.includes(kw))) continue;
        if (seen.has(kid)) continue;
        seen.add(kid);

        // 找上级章节名
        let chapterName = '';
        const unit = item.closest('.chapter_unit');
        if (unit) {
          const firstTitle = unit.querySelector(':scope > .chapter_item .chapter_Thats_bnt span[title]');
          if (firstTitle) {
            chapterName = firstTitle.getAttribute('title') || firstTitle.textContent.trim();
          }
        }
        if (!chapterName) chapterName = itemTitle || itemText;

        chapters.push({
          name: chapterName + ' - ' + (itemTitle || '测验'),
          chapterId: kid,
          knowledgeIds: [kid],
        });
      }
    }

    // 方法C: 扫描所有 input[type="checkbox"][value] 获取所有子项目ID
    if (chapters.length === 0) {
      const checkboxes = doc.querySelectorAll('.chapter_td input[type="checkbox"][value]');
      for (const cb of checkboxes) {
        const kid = cb.value;
        if (!kid || kid === '-1' || seen.has(kid)) continue;

        const item = cb.closest('.chapter_item');
        if (!item) continue;
        const itemTitle = (item.getAttribute('title') || '').trim();
        if (!isTestTitle(itemTitle)) continue;
        seen.add(kid);

        const unit = item.closest('.chapter_unit');
        let chapterName = '';
        if (unit) {
          const firstTitle = unit.querySelector(':scope > .chapter_item .chapter_Thats_bnt span[title]');
          if (firstTitle) chapterName = firstTitle.getAttribute('title') || firstTitle.textContent.trim();
        }
        chapters.push({
          name: chapterName + ' - ' + itemTitle,
          chapterId: kid,
          knowledgeIds: [kid],
        });
      }
    }

    // 方法D: 扫描章节JSON（回退方案）
    if (chapters.length === 0) {
      const scripts = doc.querySelectorAll('script');
      for (const s of scripts) {
        const text = s.textContent || '';
        for (const pat of [/(?:chapterList|chapters|chapterData)\s*[:=]\s*(\[[\s\S]*?\}\s*\])\s*[;,]/]) {
          const m = text.match(pat);
          if (m) {
            try {
              const data = JSON.parse(m[1]);
              for (const item of (Array.isArray(data) ? data : [])) {
                const nm = item.name || item.title || item.chapterName || '';
                const id = item.id || item.chapterId || '';
                if (nm && !seen.has(id || nm)) {
                  seen.add(id || nm);
                  chapters.push({ name: nm, chapterId: id, knowledgeIds: [id] });
                }
              }
            } catch (e) { /* ignore */ }
          }
        }
      }
    }

    return chapters;
  }

  function parseChaptersFromStudentStudy(doc, ci) {
    // studentstudy 页面是章节学习页面，可能包含目录结构
    return parseChaptersFromDOM(doc, ci);
  }

  function discoverFromScripts(ci) {
    const chapters = [];
    const seen = new Set();
    const scripts = document.querySelectorAll('script');
    for (const s of scripts) {
      const text = s.textContent || '';
      // 查找章节列表数据
      const patterns = [
        /(?:chapterList|chapterData|chapters|catalogList|posList)\s*[:=]\s*(\[[\s\S]*?\}\s*\])\s*[;,]/g,
        /"chapters"\s*:\s*(\[[\s\S]*?\}\s*\])/g,
        /window\.__INITIAL_STATE__\s*=\s*(\{[\s\S]*?\})\s*;/,
      ];
      for (const pat of patterns) {
        let m;
        while ((m = pat.exec(text)) !== null) {
          try {
            const data = JSON.parse(m[1]);
            const items = Array.isArray(data) ? data : (data?.chapters || data?.list || data?.items || []);
            for (const item of items) {
              const nm = item.name || item.title || item.chapterName || '';
              const id = item.id || item.chapterId || '';
              const kids = item.knowledgeIds || item.knowledgeList || item.testIds || [];
              if (nm && !seen.has(id || nm)) {
                seen.add(id || nm);
                chapters.push({ name: nm, chapterId: id, knowledgeIds: kids });
              }
            }
          } catch (e) { /* ignore */ }
        }
      }
    }
    return chapters;
  }

  function findChapterContainer(el) {
    let cur = el.parentElement;
    let depth = 0;
    while (cur && depth < 15) {
      const cls = (cur.className || '').toString();
      const tag = cur.tagName.toLowerCase();
      const dataKeys = Object.keys(cur.dataset || {});

      // 常见章节容器模式
      if (tag === 'li' || tag === 'section' || tag === 'article') return cur;
      if (/chapter|unit|catalog.*item|pos.*item|section|level[12]|node|tree.*item/i.test(cls)) return cur;
      if (cls.includes('item') || cls.includes('Item')) return cur;
      if (dataKeys.some(k => /chapter|unit|catalog|id|knowledge/i.test(k))) return cur;
      if (cur.id && /chapter|unit|catalog|pos/i.test(cur.id)) return cur;

      cur = cur.parentElement;
      depth++;
    }
    // 回退：找到最近的语义容器
    return el.closest('li, .item, .catalogItem, .treeNode, [class*="level"], div[id], div[class]') || el.closest('*[id]');
  }

  function extractChapterFromContainer(container, ci) {
    // 多选择器尝试提取标题
    const titleSels = [
      '.catalog_title', '.chapter_title', '.catalog_name', '.posName',
      '.title', '.nodeName', '.itemName', 'span.title',
      'h3', 'h4', 'h5', 'strong',
      '[class*="title"]', '[class*="Title"]', '[class*="name"]',
    ];
    let name = '';
    for (const sel of titleSels) {
      try {
        const el = container.querySelector(sel);
        if (el && el.textContent.trim().length >= 2 && !matchesTestKeyword(el.textContent.trim())) {
          name = el.textContent.trim(); break;
        }
      } catch (e) { /* skip */ }
    }
    if (!name) {
      for (const child of container.children) {
        const t = child.textContent.trim();
        if (t.length >= 2 && t.length < 150 && !matchesTestKeyword(t)) { name = t; break; }
      }
    }
    if (!name) name = container.textContent.trim().substring(0, 80);
    name = name.replace(/^第[一二三四五六七八九十\d]+[章节]/, m => m).replace(/^\d+[\.\、\s]+/, '').trim();
    if (!name) return null;

    const chapterId = container.dataset?.chapterId || container.dataset?.id || container.id ||
      container.getAttribute('data-chapterid') || container.getAttribute('data-id') || '';
    return { name, chapterId, knowledgeIds: [] };
  }

  function collectKnowledgeIds(container) {
    const ids = new Set();
    // 提取所有链接中的 knowledgeid
    const links = container.querySelectorAll('a[href]');
    for (const a of links) {
      try {
        const u = new URL(a.href, location.origin);
        const k = u.searchParams.get('knowledgeid') || u.searchParams.get('knowledgeId');
        if (k) ids.add(k);
      } catch (e) { /* skip */ }
    }
    // 提取 onclick 中的 knowledgeid
    const ocEls = container.querySelectorAll('[onclick]');
    for (const el of ocEls) {
      const m = (el.getAttribute('onclick') || '').match(/(?:knowledgeid|knowledgeId)\s*[=:'"]+\s*['"]?(\w+)/g);
      if (m) for (const mi of m) { const v = mi.match(/['"]?(\w+)$/)?.[1]; if (v) ids.add(v); }
    }
    // 提取 data-knowledgeid
    const dataEls = container.querySelectorAll('[data-knowledgeid], [data-poid]');
    for (const el of dataEls) {
      const k = el.dataset?.knowledgeid || el.dataset?.poid;
      if (k) ids.add(k);
    }
    return [...ids];
  }

  // ===================== 章节内容加载 =====================
  // 通过隐藏iframe加载页面，让页面JS自然渲染，然后由iframe内脚本提取并通过postMessage回传
  function loadChapterPage(ci, chapterId, chapterName) {
    return new Promise((resolve, reject) => {
      // 使用studentstudy URL (页面会自然加载知识卡片iframe，卡片内再加载work页面)
      const url = `https://mooc1.chaoxing.com/mycourse/studentstudy?chapterId=${chapterId}&courseId=${ci.courseId}&clazzid=${ci.clazzId}&cpi=${ci.cpi}&enc=${ci.oldenc || ci.enc}&mooc2=1`;

      log('创建iframe加载:', url.substring(0, 100));

      const iframe = document.createElement('iframe');
      iframe.style.cssText = 'position:fixed;left:-9999px;top:-9999px;width:1200px;height:800px;border:none;';
      iframe.src = url;

      let done = false;
      const timeout = 45000; // 给足够时间让嵌套iframe加载和提取

      function clean() {
        try { iframe.remove(); } catch(e) {}
      }

      // 监听来自iframe内部（及嵌套iframe）的提取结果
      function onMsg(e) {
        if (done) return;
        if (e.data && e.data.type === 'CX_EXTRACT_RESULT' && e.data.questions?.length > 0) {
          done = true;
          clearTimeout(tid);
          window.removeEventListener('message', onMsg);
          log(`[iframe加载] 收到 ${e.data.questions.length} 题 (${chapterName})`);
          clean();
          resolve({ questions: e.data.questions, chapterId });
        }
      }
      window.addEventListener('message', onMsg);

      const tid = setTimeout(() => {
        if (!done) {
          done = true;
          window.removeEventListener('message', onMsg);
          log(`[iframe加载] 超时 (${chapterName})`);
          clean();
          resolve({ questions: [], chapterId }); // 返回空结果而不是reject
        }
      }, timeout);

      iframe.onerror = () => {
        if (!done) {
          done = true;
          window.removeEventListener('message', onMsg);
          clearTimeout(tid);
          clean();
          resolve({ questions: [], chapterId });
        }
      };

      document.body.appendChild(iframe);
    });
  }

  // ===================== 题目提取 =====================
  function extractQuestions(doc) {
    // 方法1: 从 mArg 提取（最可靠）
    const mArg = parseMArg(doc);
    if (mArg) {
      const fontMap = FontDec.forDoc(doc);
      log('mArg提取 + 字体映射:', Object.keys(fontMap).length);
      const qs = extractFromMArg(mArg, fontMap);
      if (qs.length > 0) { log(`[mArg] 提取到 ${qs.length} 道题`); return qs; }
    }

    // 方法2: DOM提取
    const fontMap = FontDec.forDoc(doc);
    log('[DOM] 提取 + 字体映射:', Object.keys(fontMap).length);
    return extractFromDOM(doc, fontMap);
  }

  function extractFromDOM(doc, fontMap) {
    const questions = [];
    const seen = new Set();

    // 实际DOM: <div class="TiMu newTiMu ans-cc singleQuesId" data=... id=question...>
    let qEls = doc.querySelectorAll('.TiMu');
    if (qEls.length === 0) qEls = doc.querySelectorAll('.questionLi, .question-item, .mark_question');

    for (const el of qEls) {
      try {
        const q = parseDOMQuestion(el, doc, fontMap);
        if (!q?.stem || q.stem.length < 2) continue;
        const fp = q.stem.substring(0, 80);
        if (seen.has(fp)) continue;
        seen.add(fp);
        questions.push(q);
      } catch (e) { /* skip */ }
    }

    return questions;
  }

  function parseDOMQuestion(el, doc, fontMap) {
    // 题目唯一ID（防重），从 id="question404640058" 或 data="404640058" 提取
    const qid = (el.id || '').replace('question', '') || el.getAttribute('data') || '';
    const idPrefix = qid ? `[${qid}] ` : '';

    let stem = '';
    let type = '单选题';

    const zyTitle = el.querySelector('.Zy_TItle');
    if (zyTitle) {
      const typeSpan = zyTitle.querySelector('.newZy_TItle');
      if (typeSpan) {
        const t = typeSpan.textContent.trim();
        if (t.includes('多选')) type = '多选题';
        else if (t.includes('判断')) type = '判断题';
        else if (t.includes('填空')) type = '填空题';
        else if (t.includes('简答') || t.includes('名词')) type = '简答题';
        else type = '单选题';
      }
      // 题干文本（去掉题型标记、题号、多余空白）
      stem = zyTitle.textContent
        .replace(/【.*?】/g, '')
        .replace(/^[\s]*\d+[\s]*/, '')  // 去掉开头的题号 "1 "、"\n1\t"
        .replace(/[\t\n\r]+/g, ' ')     // 把tab/换行替换为空格
        .replace(/\s{2,}/g, ' ')        // 合并多余空格
        .trim();
    }

    if (!stem) {
      // 回退：第一个有内容的子元素
      for (const child of el.children) {
        const t = child.textContent.trim();
        if (t.length > 5 && !/^[A-Z][\.\、]/.test(t)) { stem = t; break; }
      }
    }
    if (!stem) stem = el.textContent.trim().split(/[A-Z][\.\、]/)[0].trim();

    // 选项: .Zy_ulTop 下的 li（过滤掉章节标题等非选项元素）
    const options = [];
    const ul = el.querySelector('.Zy_ulTop, ul');
    const items = ul ? ul.querySelectorAll('li') : el.querySelectorAll('li');

    for (const item of items) {
      // 必须有 i.fl（选项标签如A、B）才是真正的选项，否则是章节标题等干扰
      const iEl = item.querySelector('i.fl');
      if (!iEl) continue;
      const label = iEl.textContent.trim().replace(/[\.\、\s）\)]/g, '');
      // 标签必须是一个或两个字母（A-Z），过滤 "二、判断题" 等
      if (!/^[A-Z]{1,2}$/i.test(label)) continue;

      let text = '';
      const aEl = item.querySelector('a p');
      if (aEl) {
        text = aEl.textContent.trim();
      } else {
        text = item.textContent.trim();
        text = text.replace(/^[A-Z][\.\、\s）\)]\s*/, '').trim();
      }
      if (text) options.push({ label: label.toUpperCase(), text });
    }

    // 答案提取 — 优先正确答案，做错的题「我的答案」≠「正确答案」
    let answer = '';
    // 1. 先找正确答案元素
    let correctEl = el.querySelector('.correctAnswer .answerCon, .correctAnswerBx .correctAnswer, .rightAnswerContent, .mark_key, .right_answer');
    if (!correctEl) {
      // 2. 找成绩标记 — 如果得了满分，我的答案就是正确答案
      const markingDui = el.querySelector('.marking_dui');
      const scoreEl = el.querySelector('.newAnswerScore .scoreNum');
      if (markingDui || (scoreEl && parseFloat(scoreEl.textContent) > 0)) {
        correctEl = el.querySelector('.answerCon, .myAnswer .fl.answerCon');
      }
    }
    // 3. 最后回退
    if (!correctEl) correctEl = el.querySelector('.answerCon, .myAnswer .fl.answerCon, .mark_answer');
    if (correctEl) answer = correctEl.textContent.trim();

    // 清理答案格式：去掉"正确答案："等前缀，只保留字母或文字
    answer = answer
      .replace(/^(正确答案|答案|我的答案)[：:]\s*/i, '')
      .replace(/^[对✔✓Tt]rue$/i, '正确')
      .replace(/^[错✗✘Ff]alse$/i, '错误')
      .trim();

    // 解析
    let analysis = '';
    const alEl = el.querySelector('.analysis, .answerAnalysis, .explain, [class*="analysis"]');
    if (alEl) {
      analysis = alEl.textContent.trim().replace(/^(解析[：:]|答案解析[：:]|题目解析[：:])/, '');
    }

    // 清理所有文本字段
    const clean = (s) => (s || '')
      .replace(/[\u00A0]/g, ' ')   // &nbsp; → 空格
      .replace(/[\t\n\r]+/g, ' ')  // 制表符/换行 → 空格
      .replace(/\s{2,}/g, ' ')     // 合并多余空格
      .trim();

    return {
      type,
      stem: idPrefix + clean(FontDec.apply(stem, fontMap)),
      options: options.map(o => ({ label: o.label, text: clean(FontDec.apply(o.text, fontMap)) })),
      answer: clean(FontDec.apply(answer, fontMap)),
      analysis: clean(FontDec.apply(analysis, fontMap)),
    };
  }

  // ===================== 主流程 =====================
  async function start(ci) {
    S.running = true; S.stopped = false; S.results = [];
    upProgress('正在发现章节测验...', 2);

    let chapters;
    try {
      chapters = await discoverChapters(ci);
    } catch (e) {
      upStatus('❌ ' + e.message, 'error');
      S.running = false;
      return;
    }

    S.chapters = chapters; S.totalCh = chapters.length; S.doneCh = 0;
    if (chapters.length === 0) {
      upStatus('⚠️ 未发现含有章节测验的内容。请确认课程页面已加载完毕且含有章节测验。', 'warn');
      S.running = false;
      return;
    }

    upStatus(`发现 ${chapters.length} 个章节，开始提取...`, 'info');

    for (let i = 0; i < chapters.length; i++) {
      if (S.stopped) break;
      S.curChIdx = i;
      const ch = chapters[i];
      const pct = 5 + Math.floor(85 * (i / chapters.length));
      upProgress(`[${i + 1}/${chapters.length}] ${ch.name}`, pct);

      const cr = { chapterName: ch.name, questions: [] };

      // 使用 chapterId 加载 studentstudy 页面
      const cid = ch.chapterId || (ch.knowledgeIds.length > 0 ? ch.knowledgeIds[0] : null);
      if (cid) {
        try {
          const result = await loadChapterPage(ci, cid, ch.name);
          cr.questions.push(...result.questions);
          await randDelay(CONF.delayCh);
        } catch (e) {
          log(`加载章节失败 ${ch.name}:`, e.message);
        }
      }

      if (cr.questions.length > 0) {
        S.results.push(cr);
        S.totalQ += cr.questions.length;
      }
      S.doneCh++;
    }

    S.running = false;
    const totalQ = S.results.reduce((s, r) => s + r.questions.length, 0);
    upProgress('提取完成！', 100);
    if (totalQ > 0) {
      upStatus(`✅ 提取完成！共 ${S.results.length} 个章节，${totalQ} 道题目`, 'success');
      enableBtns();
    } else {
      upStatus('⚠️ 提取完成但未获取到题目。可能原因：\n1. 章节测验尚未完成（需先做完测验才能查看答案）\n2. 页面结构不匹配', 'warn');
    }
  }

  function stop() {
    S.stopped = true; S.running = false;
    upStatus('⏹ 已停止提取', 'info');
  }

  // ===================== 导出 =====================
  function toText() {
    const bar = '═'.repeat(50);
    let t = `╔${bar}╗\n`;
    t += `║  课程：${S.courseInfo?.name || '未知'}\n`;
    t += `║  时间：${new Date().toLocaleString()}\n`;
    t += `║  共 ${S.results.length} 个章节，${S.totalQ} 道题目\n`;
    t += `╚${bar}╝\n\n`;

    let qi = 0;
    for (const ch of S.results) {
      t += `\n┌${'─'.repeat(48)}┐\n`;
      t += `│ ${ch.chapterName}（${ch.questions.length}题）\n`;
      t += `└${'─'.repeat(48)}┘\n\n`;

      for (const q of ch.questions) {
        qi++;
        const typeTag = q.type === '单选题' ? '[单选]' : q.type === '多选题' ? '[多选]' : q.type === '判断题' ? '[判断]' : q.type === '填空题' ? '[填空]' : '[简答]';
        t += `  ${qi}. ${typeTag} ${q.stem}\n`;
        for (const o of q.options) t += `       ${o.label}. ${o.text}\n`;
        if (q.options.length > 0) t += '\n';
        if (q.answer) t += `  ▶ 答案：${q.answer}\n`;
        if (q.analysis) t += `  ✎ 解析：${q.analysis}\n`;
        t += '\n';
      }
    }
    return t;
  }

  function downloadTxt() {
    const blob = new Blob(['\uFEFF' + toText()], { type: 'text/plain;charset=utf-8' });
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = `${(S.courseInfo?.name || '题库').replace(/[\\/:*?"<>|]/g, '_')}_章节测验.txt`;
    a.click(); URL.revokeObjectURL(a.href);
  }

  async function copyText() {
    try {
      await navigator.clipboard.writeText(toText());
      toast('✅ 已复制到剪贴板');
    } catch (e) {
      const ta = document.createElement('textarea');
      ta.value = toText(); ta.style.cssText = 'position:fixed;left:-9999px;';
      document.body.appendChild(ta); ta.select();
      document.execCommand('copy'); ta.remove();
      toast('✅ 已复制到剪贴板');
    }
  }

  function downloadJson() {
    const data = {
      courseName: S.courseInfo?.name || '',
      extractTime: new Date().toISOString(),
      totalChapters: S.results.length,
      totalQuestions: S.totalQ,
      chapters: S.results,
    };
    const blob = new Blob([JSON.stringify(data, null, 2)], { type: 'application/json' });
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = `${(S.courseInfo?.name || '题库').replace(/[\\/:*?"<>|]/g, '_')}_章节测验.json`;
    a.click(); URL.revokeObjectURL(a.href);
  }

  // MD导出
  function toMarkdown() {
    let t = '';
    t += `# ${S.courseInfo?.name || '未知课程'} - 章节测验题库\n\n`;
    t += `> 提取时间：${new Date().toLocaleString()}  \n`;
    t += `> 共 **${S.results.length}** 个章节，**${S.totalQ}** 道题目\n\n`;

    let qi = 0;
    for (const ch of S.results) {
      t += `---\n\n## ${ch.chapterName}（${ch.questions.length}题）\n\n`;
      for (const q of ch.questions) {
        qi++;
        const typeEmoji = { '单选题': '🔘', '多选题': '☑️', '判断题': '⚖️', '填空题': '📝', '简答题': '📃' };
        t += `### ${qi}. [${q.type}] ${q.stem}\n\n`;

        // 选项
        for (const o of q.options) {
          t += `- **${o.label}.** ${o.text}\n`;
        }

        if (q.options.length > 0) t += '\n';

        // 答案
        if (q.answer) {
          t += `> ✅ **答案**：${q.answer}\n`;
        }
        // 解析
        if (q.analysis) {
          t += `> 📝 **解析**：${q.analysis}\n`;
        }
        t += '\n';
      }
    }
    return t;
  }

  function downloadMarkdown() {
    log('[MD] 开始生成...');
    const md = toMarkdown();
    log('[MD] 生成完成,', md.length, '字符');
    const blob = new Blob(['\uFEFF' + md], { type: 'text/plain;charset=utf-8' });
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = `${(S.courseInfo?.name || '题库').replace(/[\\/:*?"<>|]/g, '_')}_章节测验.md`;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    setTimeout(() => URL.revokeObjectURL(a.href), 100);
    toast('✅ MD已下载');
  }

  // ===================== XLSX生成（严格按模板格式） =====================
  // 模板列: A=试题类型 B=试题题目 C=参考答案 D=A选项 E=B选项 F=C选项 G=D选项 H=E选项 I=F选项 J=G选项 K=章节 L=解析
  function buildXlsxBlob() {
    const typeMap = { '单选题': '单选', '多选题': '多选', '判断题': '判断', '填空题': '填空', '简答题': '简答' };
    const optLabels = ['A','B','C','D','E','F','G'];

    // 第一遍：统计最大选项数
    let maxOpts = 0;
    const dataRows = [];
    for (const ch of S.results) {
      for (const q of ch.questions) {
        let answer = (q.answer || '').replace(/^(正确答案|答案|我的答案)[：:]\s*/i, '').trim();
        if (q.type === '单选题') answer = (answer.match(/[A-Z]/i)?.[0] || answer).toUpperCase();
        if (q.type === '多选题') answer = answer.replace(/[^A-Za-z]/g, '').toUpperCase();
        if (q.type === '判断题') answer = /^(正确|对|✔|✓|T|True|Y|Yes)$/i.test(answer) ? '正确' : '错误';

        const opts = [];
        if (q.type === '判断题' && q.options.length === 0) {
          opts.push('正确', '错误');
        } else {
          for (const o of q.options) opts.push(o.text || '');
        }
        maxOpts = Math.max(maxOpts, opts.length);

        const chapterParts = ch.chapterName.split(' - ').slice(0, 2);
        const chName = chapterParts.length > 1 ? `${chapterParts[0]}~${chapterParts[1]}` : ch.chapterName;

        dataRows.push({ type: typeMap[q.type] || q.type, stem: q.stem, answer, opts, chapter: chName, analysis: q.analysis || null });
      }
    }

    const optCols = Math.max(4, Math.min(maxOpts, 7)); // 至少4列，最多7列

    // 表头
    const header = ['试题类型', '试题题目', '参考答案'];
    for (let i = 0; i < optCols; i++) header.push(optLabels[i] + '选项');
    header.push('章节', '解析');

    // 数据行
    const rows = [header];
    for (const dr of dataRows) {
      const row = [dr.type, dr.stem, dr.answer];
      for (let i = 0; i < optCols; i++) row.push(dr.opts[i] || null);
      row.push(dr.chapter, dr.analysis);
      rows.push(row);
    }

    return buildXlsxFile(rows, optCols);
  }

  // 构建 XLSX（ZIP包，内联字符串，STORED无压缩）
  function buildXlsxFile(rows, optCols) {
    const esc = (s) => String(s ?? '').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;').replace(/\r/g, '').replace(/\n/g, '&#10;');

    const totalCols = 3 + optCols + 2; // 题型+题目+答案 + N选项 + 章节+解析
    const cols = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';

    // 列宽：题型10, 题目60, 答案20, 选项30each, 章节20, 解析40
    let colXml = '<cols>';
    colXml += '<col min="1" max="1" width="10"/>';
    colXml += '<col min="2" max="2" width="60"/>';
    colXml += '<col min="3" max="3" width="20"/>';
    const optStart = 4, optEnd = 3 + optCols;
    colXml += `<col min="${optStart}" max="${optEnd}" width="30"/>`;
    colXml += `<col min="${optEnd+1}" max="${optEnd+1}" width="20"/>`;
    colXml += `<col min="${optEnd+2}" max="${optEnd+2}" width="40"/>`;
    colXml += '</cols>';

    let sheetXml = `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">${colXml}<sheetData>`;

    for (let ri = 0; ri < rows.length; ri++) {
      sheetXml += `<row r="${ri + 1}">`;
      for (let ci = 0; ci < rows[ri].length; ci++) {
        const val = rows[ri][ci];
        if (val !== null && val !== undefined) {
          const ref = cols[ci] + (ri + 1);
          sheetXml += `<c r="${ref}" t="str"><v>${esc(String(val))}</v></c>`;
        }
      }
      sheetXml += '</row>';
    }
    sheetXml += '</sheetData></worksheet>';

    // styles.xml (minimal)
    const stylesXml = '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><styleSheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main"><fonts count="2"><font><sz val="11"/></font><font><b/><sz val="11"/></font></fonts><fills count="2"><fill><patternFill patternType="none"/></fill><fill><patternFill patternType="gray125"/></fill></fills><borders count="1"><border/></borders><cellStyleXfs count="1"><xf numFmtId="0" fontId="0" fillId="0" borderId="0"/></cellStyleXfs><cellXfs count="2"><xf numFmtId="0" fontId="0" fillId="0" borderId="0"/><xf numFmtId="0" fontId="1" fillId="0" borderId="0"/></cellXfs></styleSheet>';

    // sharedStrings.xml (empty - using inline strings)
    const sstXml = '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><sst xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" count="0" uniqueCount="0"/>';

    // workbook.xml
    const wbXml = '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships"><sheets><sheet name="题库" sheetId="1" r:id="rId1"/></sheets></workbook>';

    // workbook.xml.rels
    const wbRelsXml = '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" Target="worksheets/sheet1.xml"/><Relationship Id="rId2" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles" Target="styles.xml"/><Relationship Id="rId3" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/sharedStrings" Target="sharedStrings.xml"/></Relationships>';

    // [Content_Types].xml
    const ctXml = '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types"><Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/><Default Extension="xml" ContentType="application/xml"/><Override PartName="/xl/workbook.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/><Override PartName="/xl/worksheets/sheet1.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/><Override PartName="/xl/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.styles+xml"/><Override PartName="/xl/sharedStrings.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sharedStrings+xml"/></Types>';

    // _rels/.rels
    const relsXml = '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="xl/workbook.xml"/></Relationships>';

    // --- ZIP构建（STORED无压缩） ---
    const files = [
      { name: '[Content_Types].xml', data: ctXml },
      { name: '_rels/.rels', data: relsXml },
      { name: 'xl/workbook.xml', data: wbXml },
      { name: 'xl/_rels/workbook.xml.rels', data: wbRelsXml },
      { name: 'xl/worksheets/sheet1.xml', data: sheetXml },
      { name: 'xl/styles.xml', data: stylesXml },
      { name: 'xl/sharedStrings.xml', data: sstXml },
    ];

    return buildZip(files);
  }

  // 最小ZIP构建器（STORED方法，无压缩）
  function buildZip(files) {
    const encoder = new TextEncoder();

    // CRC32 table
    const crcTable = new Uint32Array(256);
    for (let i = 0; i < 256; i++) {
      let c = i;
      for (let j = 0; j < 8; j++) c = (c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1);
      crcTable[i] = c;
    }
    function crc32(data) {
      let c = 0xFFFFFFFF;
      for (let i = 0; i < data.length; i++) c = crcTable[(c ^ data[i]) & 0xFF] ^ (c >>> 8);
      return (c ^ 0xFFFFFFFF) >>> 0;
    }

    const localHeaders = [];
    const centralHeaders = [];
    let offset = 0;

    for (const file of files) {
      const nameBytes = encoder.encode(file.name);
      const dataBytes = encoder.encode(file.data);
      const crc = crc32(dataBytes);
      const size = dataBytes.length;

      // Local file header
      const lh = new Uint8Array(30 + nameBytes.length);
      const lhView = new DataView(lh.buffer);
      lhView.setUint32(0, 0x04034b50, true); // signature
      lhView.setUint16(4, 20, true);          // version
      lhView.setUint16(6, 0, true);           // flags
      lhView.setUint16(8, 0, true);           // method (STORED)
      lhView.setUint32(10, 0, true);          // mod time (unused)
      lhView.setUint32(14, crc, true);
      lhView.setUint32(18, size, true);       // compressed size
      lhView.setUint32(22, size, true);       // uncompressed size
      lhView.setUint16(26, nameBytes.length, true);
      lhView.setUint16(28, 0, true);          // extra field length
      lh.set(nameBytes, 30);
      localHeaders.push({ header: lh, data: dataBytes, offset: offset });
      offset += lh.length + size;

      // Central directory header
      const ch = new Uint8Array(46 + nameBytes.length);
      const chView = new DataView(ch.buffer);
      chView.setUint32(0, 0x02014b50, true);  // signature
      chView.setUint16(4, 20, true);
      chView.setUint16(6, 20, true);
      chView.setUint16(8, 0, true);
      chView.setUint16(10, 0, true);
      chView.setUint32(12, 0, true);
      chView.setUint32(16, crc, true);
      chView.setUint32(20, size, true);
      chView.setUint32(24, size, true);
      chView.setUint16(28, nameBytes.length, true);
      chView.setUint16(30, 0, true);
      chView.setUint16(32, 0, true);
      chView.setUint16(34, 0, true);
      chView.setUint32(36, 0, true);
      chView.setUint32(40, 0, true);
      chView.setUint32(42, localHeaders[localHeaders.length - 1].offset, true);
      ch.set(nameBytes, 46);
      centralHeaders.push(ch);
    }

    // End of central directory record
    const cdOffset = offset;
    let cdSize = 0;
    for (const ch of centralHeaders) cdSize += ch.length;

    const eocd = new Uint8Array(22);
    const eocdView = new DataView(eocd.buffer);
    eocdView.setUint32(0, 0x06054b50, true);
    eocdView.setUint16(4, 0, true);
    eocdView.setUint16(6, 0, true);
    eocdView.setUint16(8, files.length, true);
    eocdView.setUint16(10, files.length, true);
    eocdView.setUint32(12, cdSize, true);
    eocdView.setUint32(16, cdOffset, true);
    eocdView.setUint16(20, 0, true);

    // Assemble
    const totalSize = cdOffset + cdSize + 22;
    const result = new Uint8Array(totalSize);
    let pos = 0;
    for (const lh of localHeaders) {
      result.set(lh.header, pos); pos += lh.header.length;
      result.set(lh.data, pos); pos += lh.data.length;
    }
    for (const ch of centralHeaders) { result.set(ch, pos); pos += ch.length; }
    result.set(eocd, pos);

    return new Blob([result], { type: 'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet' });
  }

  function downloadXlsx() {
    try {
      log('[XLSX] 开始生成...');
      const blob = buildXlsxBlob();
      log('[XLSX] 生成完成,', blob.size, 'bytes');
      const a = document.createElement('a');
      a.href = URL.createObjectURL(blob);
      a.download = `${(S.courseInfo?.name || '题库').replace(/[\\/:*?"<>|]/g, '_')}_章节测验.xlsx`;
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
      setTimeout(() => URL.revokeObjectURL(a.href), 100);
      toast('✅ XLSX已下载');
    } catch (e) {
      log('[XLSX] 错误:', e.message, e.stack);
      toast('❌ XLSX导出失败: ' + e.message);
    }
  }

  // ===================== UI =====================
  let panel, pbar, statusEl, startBtn, stopBtn, txtBtn, copyBtn, jsonBtn, singleBtn, diagBtn, mdBtn, xlsxBtn;

  function createUI() {
    const css = document.createElement('style');
    css.textContent = `
.cx-p{position:fixed;right:20px;top:80px;z-index:2147483647;width:${CONF.panelWidth}px;background:#fff;border-radius:12px;box-shadow:0 8px 32px rgba(0,0,0,.18);font:14px/1.5 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;color:#333;user-select:none;transition:all .3s;}
.cx-p.cx-collapsed{transform:translateX(${CONF.panelWidth - 40}px);}
.cx-h{display:flex;align-items:center;padding:12px 16px;border-bottom:1px solid #eee;cursor:move;border-radius:12px 12px 0 0;background:linear-gradient(135deg,#667eea,#764ba2);color:#fff;}
.cx-h h3{margin:0;font-size:15px;flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;}
.cx-h button{background:none;border:none;color:#fff;cursor:pointer;font-size:20px;padding:0 8px;line-height:1;}
.cx-h button:hover{background:rgba(255,255,255,.2);border-radius:4px;}
.cx-b{padding:16px;}
.cx-b.cx-hidden{display:none;}
.cx-info{margin-bottom:8px;font-size:13px;color:#666;}
.cx-info strong{color:#333;}
.cx-pw{margin:10px 0;}
.cx-pb{height:6px;background:#e9ecef;border-radius:3px;overflow:hidden;}
.cx-pf{height:100%;background:linear-gradient(90deg,#667eea,#764ba2);border-radius:3px;transition:width .5s;width:0;}
.cx-pt{font-size:12px;color:#999;margin-top:4px;}
.cx-s{padding:8px 12px;border-radius:6px;font-size:13px;margin-bottom:12px;line-height:1.6;white-space:pre-wrap;}
.cx-s.info{background:#e3f2fd;color:#1565c0;}
.cx-s.success{background:#e8f5e9;color:#2e7d32;}
.cx-s.error{background:#ffebee;color:#c62828;}
.cx-s.warn{background:#fff3e0;color:#e65100;}
.cx-br{display:flex;gap:8px;flex-wrap:wrap;}
.cx-btn{padding:8px 16px;border:none;border-radius:6px;cursor:pointer;font-size:14px;font-weight:500;transition:all .2s;}
.cx-btn:disabled{opacity:.45;cursor:not-allowed;pointer-events:none;}
.cx-primary{background:linear-gradient(135deg,#667eea,#764ba2);color:#fff;}
.cx-primary:hover:not(:disabled){box-shadow:0 4px 12px rgba(102,126,234,.4);}
.cx-danger{background:#e74c3c;color:#fff;}
.cx-danger:hover:not(:disabled){background:#c0392b;}
.cx-outline{background:#fff;color:#667eea;border:1px solid #667eea;}
.cx-outline:hover:not(:disabled){background:#f5f0ff;}
.cx-sm{padding:6px 12px;font-size:13px;}
.cx-toast{position:fixed;top:20px;left:50%;transform:translateX(-50%);z-index:2147483999;background:rgba(0,0,0,.82);color:#fff;padding:12px 28px;border-radius:8px;font-size:14px;animation:cx-fade .3s;}
@keyframes cx-fade{from{opacity:0;transform:translateX(-50%) translateY(-10px)}to{opacity:1;transform:translateX(-50%) translateY(0)}}
    `;
    document.head.appendChild(css);

    panel = document.createElement('div');
    panel.className = 'cx-p';
    panel.innerHTML = `
<div class="cx-h" id="cx-head"><h3>📚 章节测验提取器</h3><button id="cx-collapse">−</button></div>
<div class="cx-b" id="cx-body">
  <div class="cx-info">课程：<strong id="cx-cname">检测中...</strong></div>
  <div class="cx-info">章节：<strong id="cx-ccount">--</strong></div>
  <div class="cx-pw"><div class="cx-pb"><div class="cx-pf" id="cx-pbar"></div></div><div class="cx-pt" id="cx-ptext">就绪</div></div>
  <div class="cx-s info" id="cx-status">点击「开始提取」自动提取所有章节测验题目。</div>
  <div class="cx-kw-wrap" style="display:none" id="cx-kw-wrap">
    <div style="font-size:12px;color:#666;margin-bottom:4px">🔑 匹配关键词（title包含任一即判定为测验）</div>
    <div style="display:flex;gap:4px;margin-bottom:6px">
      <input id="cx-kw-input" style="flex:1;padding:4px 8px;border:1px solid #ddd;border-radius:4px;font-size:12px" placeholder="输入关键词，回车添加">
      <button class="cx-btn cx-outline cx-sm" id="cx-kw-add" style="font-size:11px;padding:4px 8px;white-space:nowrap">+添加</button>
    </div>
    <div id="cx-kw-tags" style="display:flex;flex-wrap:wrap;gap:4px;margin-bottom:4px"></div>
    <button class="cx-btn cx-outline cx-sm" id="cx-kw-reset" style="font-size:10px;padding:2px 8px">恢复默认</button>
  </div>
  <div class="cx-ai-wrap" style="display:none" id="cx-ai-wrap">
    <div style="font-size:12px;color:#666;margin-bottom:6px">🤖 AI智能生成解析（OpenAI兼容API）</div>
    <input id="cx-ai-url" style="width:100%;padding:4px 8px;border:1px solid #ddd;border-radius:4px;font-size:12px;margin-bottom:4px;box-sizing:border-box" placeholder="API地址，如 https://api.deepseek.com/v1">
    <input id="cx-ai-key" style="width:100%;padding:4px 8px;border:1px solid #ddd;border-radius:4px;font-size:12px;margin-bottom:4px;box-sizing:border-box" placeholder="API Key">
    <input id="cx-ai-model" style="width:100%;padding:4px 8px;border:1px solid #ddd;border-radius:4px;font-size:12px;margin-bottom:6px;box-sizing:border-box" placeholder="模型名，如 deepseek-chat">
    <div style="display:flex;align-items:center;gap:8px;margin-bottom:6px">
      <label style="font-size:12px;color:#666;display:flex;align-items:center;gap:4px"><input type="checkbox" id="cx-ai-enable"> 仅生成缺失解析</label>
    </div>
    <button class="cx-btn cx-primary cx-sm" id="cx-ai-run" disabled>🤖 开始生成解析</button>
    <span id="cx-ai-progress" style="font-size:12px;color:#999;margin-left:8px"></span>
  </div>
  <div class="cx-br">
    <button class="cx-btn cx-primary" id="cx-start">▶ 自动提取全部</button>
    <button class="cx-btn cx-outline cx-sm" id="cx-single" style="background:#e8f5e9">📄 提取当前页</button>
    <button class="cx-btn cx-outline cx-sm" id="cx-diag" style="font-size:11px">🔍 诊断</button>
    <button class="cx-btn cx-outline cx-sm" id="cx-kw-toggle" style="font-size:11px">⚙️ 关键词</button>
    <button class="cx-btn cx-outline cx-sm" id="cx-ai-toggle" style="font-size:11px">🤖 AI解析</button>
    <button class="cx-btn cx-danger" id="cx-stop" disabled>⏹ 停止</button>
    <button class="cx-btn cx-outline cx-sm" id="cx-md" disabled>📝 MD</button>
    <button class="cx-btn cx-outline cx-sm" id="cx-txt" disabled>📥 TXT</button>
    <button class="cx-btn cx-outline cx-sm" id="cx-xlsx" disabled>📊 XLSX</button>
    <button class="cx-btn cx-outline cx-sm" id="cx-copy" disabled>📋 复制</button>
  </div>
</div>`;

    document.body.appendChild(panel);

    pbar = document.getElementById('cx-pbar');
    statusEl = document.getElementById('cx-status');
    startBtn = document.getElementById('cx-start');
    stopBtn = document.getElementById('cx-stop');
    txtBtn = document.getElementById('cx-txt');
    copyBtn = document.getElementById('cx-copy');
    jsonBtn = document.getElementById('cx-json');
    mdBtn = document.getElementById('cx-md');
    xlsxBtn = document.getElementById('cx-xlsx');
    singleBtn = document.getElementById('cx-single');
    diagBtn = document.getElementById('cx-diag');

    // 关键词管理
    const kwWrap = document.getElementById('cx-kw-wrap');
    const kwToggle = document.getElementById('cx-kw-toggle');
    const kwInput = document.getElementById('cx-kw-input');
    const kwAdd = document.getElementById('cx-kw-add');
    const kwTags = document.getElementById('cx-kw-tags');
    const kwReset = document.getElementById('cx-kw-reset');

    function renderKwTags() {
      if (!kwTags) return;
      const keywords = getKeywords();
      kwTags.innerHTML = keywords.map(k =>
        `<span style="display:inline-flex;align-items:center;gap:2px;background:#f0f0f0;padding:2px 6px;border-radius:4px;font-size:12px">${k}<span style="cursor:pointer;color:#999;margin-left:2px" data-kw="${k}">×</span></span>`
      ).join('');
      // 删除事件
      kwTags.querySelectorAll('span[data-kw]').forEach(s => {
        s.addEventListener('click', () => {
          const k = s.getAttribute('data-kw');
          const list = getKeywords().filter(x => x !== k);
          if (list.length > 0) { saveKeywords(list); renderKwTags(); }
        });
      });
    }

    function addKeyword(k) {
      const kw = k.trim();
      if (!kw) return;
      const list = getKeywords();
      if (!list.includes(kw)) { list.push(kw); saveKeywords(list); renderKwTags(); }
      if (kwInput) kwInput.value = '';
    }

    if (kwToggle) kwToggle.addEventListener('click', () => {
      const vis = kwWrap.style.display !== 'none';
      kwWrap.style.display = vis ? 'none' : 'block';
      kwToggle.textContent = vis ? '⚙️ 关键词' : '⚙️ 收起';
      if (!vis) renderKwTags();
    });
    if (kwAdd) kwAdd.addEventListener('click', () => addKeyword(kwInput?.value));
    if (kwInput) kwInput.addEventListener('keydown', e => { if (e.key === 'Enter') addKeyword(kwInput.value); });
    if (kwReset) kwReset.addEventListener('click', () => { saveKeywords([...DEFAULT_KEYWORDS]); renderKwTags(); });

    // AI设置管理
    const aiWrap = document.getElementById('cx-ai-wrap');
    const aiToggle = document.getElementById('cx-ai-toggle');
    const aiUrl = document.getElementById('cx-ai-url');
    const aiKey = document.getElementById('cx-ai-key');
    const aiModel = document.getElementById('cx-ai-model');
    const aiEnable = document.getElementById('cx-ai-enable');
    const aiRun = document.getElementById('cx-ai-run');
    const aiProgress = document.getElementById('cx-ai-progress');

    function getAiConfig() {
      try { return JSON.parse(GM_getValue('cx_ai_config', '{}')); } catch(e) { return {}; }
    }
    function saveAiConfig(cfg) { GM_setValue('cx_ai_config', JSON.stringify(cfg)); }
    function loadAiConfig() {
      const cfg = getAiConfig();
      if (aiUrl) aiUrl.value = cfg.url || 'https://api.deepseek.com/v1';
      if (aiKey) aiKey.value = cfg.key || '';
      if (aiModel) aiModel.value = cfg.model || 'deepseek-chat';
      if (aiEnable) aiEnable.checked = cfg.onlyMissing !== false;
    }
    function onAiConfigChange() {
      saveAiConfig({ url: aiUrl?.value || '', key: aiKey?.value || '', model: aiModel?.value || '', onlyMissing: aiEnable?.checked !== false });
    }
    if (aiUrl) aiUrl.addEventListener('input', onAiConfigChange);
    if (aiKey) aiKey.addEventListener('input', onAiConfigChange);
    if (aiModel) aiModel.addEventListener('input', onAiConfigChange);
    if (aiEnable) aiEnable.addEventListener('change', onAiConfigChange);
    loadAiConfig();

    if (aiToggle) aiToggle.addEventListener('click', () => {
      const vis = aiWrap.style.display !== 'none';
      aiWrap.style.display = vis ? 'none' : 'block';
      aiToggle.textContent = vis ? '🤖 AI解析' : '🤖 收起';
      if (!vis) { loadAiConfig(); updateAiBtn(); }
    });

    function updateAiBtn() {
      if (aiRun) {
        const cfg = getAiConfig();
        aiRun.disabled = !cfg.key || !cfg.url || S.totalQ === 0;
      }
    }

    // AI生成解析
    async function aiGenerate() {
      const cfg = getAiConfig();
      if (!cfg.key || !cfg.url) { upStatus('❌ 请先填写 API 地址和 Key', 'error'); return; }

      const onlyMissing = cfg.onlyMissing !== false;
      let todo = [];
      for (const ch of S.results) {
        for (const q of ch.questions) {
          if (onlyMissing && q.analysis && q.analysis.trim()) continue;
          // 跳过简单判断题
          if (q.type === '判断题' && q.analysis) continue;
          todo.push(q);
        }
      }

      if (todo.length === 0) { upStatus('✅ 所有题目已有解析', 'success'); return; }

      aiRun.disabled = true;
      let done = 0;

      for (const q of todo) {
        const prompt = `你是学习通课程助教。请为下面这道题目写一段简短的解析（50-150字），解释为什么正确答案是对的，帮助理解知识点。\n\n题型：${q.type}\n题目：${q.stem}\n选项：${q.options.map(o => o.label + '. ' + o.text).join('；')}\n正确答案：${q.answer}\n\n请直接输出解析内容，不要加前缀。`;

        try {
          const resp = await callAiApi(cfg, prompt);
          q.analysis = resp;
        } catch(e) {
          log('[AI] 生成失败:', e.message);
          q.analysis = '';
        }
        done++;
        if (aiProgress) aiProgress.textContent = `${done}/${todo.length}`;
        await sleep(800); // 限速
      }

      aiRun.disabled = false;
      upStatus(`✅ AI解析完成！${done}道题目已处理\n\n解析已写入内存，请点击「📊 XLSX」或「📝 MD」重新导出。`, 'success');
      if (aiProgress) aiProgress.textContent = '';
    }

    function callAiApi(cfg, prompt) {
      const url = (cfg.url || '').replace(/\/+$/, '') + '/chat/completions';
      return fetch(url, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          'Authorization': 'Bearer ' + cfg.key,
        },
        body: JSON.stringify({
          model: cfg.model || 'deepseek-chat',
          messages: [{ role: 'user', content: prompt }],
          max_tokens: 500,
          temperature: 0.3,
        }),
        signal: AbortSignal.timeout(30000),
      }).then(r => {
        if (!r.ok) throw new Error('HTTP ' + r.status);
        return r.json();
      }).then(json => {
        const content = json?.choices?.[0]?.message?.content?.trim();
        if (content) return content;
        throw new Error('AI返回为空: ' + (json?.error?.message || ''));
      });
    }

    if (aiRun) aiRun.addEventListener('click', aiGenerate);

    // 提取完成后启用AI按钮
    const origEnableBtns = enableBtns;
    enableBtns = function() {
      origEnableBtns();
      updateAiBtn();
    };

    if (diagBtn) diagBtn.addEventListener('click', () => {
      console.log('=== CX诊断 ===');
      console.log('URL:', location.href);
      console.log('divs:', document.querySelectorAll('div').length, '.TiMu:', document.querySelectorAll('.TiMu').length);
      const iframes = document.querySelectorAll('iframe');
      console.log('iframes:', iframes.length);
      iframes.forEach((f, i) => {
        console.log(`  [${i}] src:`, (f.src || '').substring(0, 200), 'sandbox:', f.getAttribute('sandbox'));
        try {
          const d = f.contentDocument || f.contentWindow.document;
          console.log(`  [${i}] 可访问:`, !!d?.body, 'divs:', d?.querySelectorAll?.('div')?.length, '.TiMu:', d?.querySelectorAll?.('.TiMu')?.length);
          if (d?.body) console.log(`  [${i}] body:`, d.body.innerHTML.substring(0, 500));
        } catch (e) { console.log(`  [${i}] 错误:`, e.message); }
      });
      console.log('=== END ===');
      upStatus('诊断完成，查看F12控制台', 'info');
    });

    // 提取当前页
    if (singleBtn) singleBtn.addEventListener('click', async () => {
      if (S.running) return;
      singleBtn.disabled = true;
      upStatus('正在提取当前页面...', 'info');
      upProgress('提取中...', 30);
      try {
        // 先查主文档，再查所有可访问的同源iframe
        let qs = extractQuestions(document);
        log('[单页] 主文档:', qs.length, '题');

        if (qs.length === 0) {
          const iframes = document.querySelectorAll('iframe');
          for (const iframe of iframes) {
            try {
              const idoc = iframe.contentDocument || iframe.contentWindow.document;
              if (idoc?.body) {
                qs = extractQuestions(idoc);
                log('[单页] iframe:', qs.length, '题');
                if (qs.length > 0) break;
                // 嵌套iframe
                for (const i2 of idoc.querySelectorAll('iframe')) {
                  try {
                    const i2doc = i2.contentDocument || i2.contentWindow.document;
                    if (i2doc?.body) {
                      qs = extractQuestions(i2doc);
                      if (qs.length > 0) break;
                    }
                  } catch (e2) { }
                }
                if (qs.length > 0) break;
              }
            } catch (e) { /* cross-origin */ }
          }
        }

        if (qs.length > 0) {
          let chName = '当前页面';
          const prevTitle = document.querySelector('.prev_title');
          const hTitle = document.querySelector('h3, h4, .chapterTitle, .title, .prev_title');
          if (hTitle) chName = hTitle.textContent.trim().substring(0, 50);

          const existing = S.results.find(r => r.chapterName === chName);
          if (existing) { existing.questions.push(...qs); }
          else { S.results.push({ chapterName: chName, questions: qs }); }
          S.totalQ = S.results.reduce((s, r) => s + r.questions.length, 0);
          upProgress('提取完成！', 100);
          upStatus(`✅ 提取到 ${qs.length} 题 (累计${S.totalQ}题)`, 'success');
          enableBtns();
        } else {
          upStatus('⚠️ 当前页面未检测到题目。\n请确认：\n1. 已进入测验页面且能看到题目\n2. 测验已经完成（才能看到答案）\n\n如题目在页面中可见但未检测到，\n请截图告知页面结构。', 'warn');
          upProgress('就绪', 0);
        }
      } catch (e) {
        upStatus('❌ 提取失败: ' + e.message, 'error');
        upProgress('就绪', 0);
      }
      singleBtn.disabled = false;
    });

    if (startBtn) startBtn.addEventListener('click', async () => {
      if (S.running) return;
      startBtn.disabled = true;
      singleBtn.disabled = true;
      stopBtn.disabled = false;
      S.courseInfo = S.courseInfo || getCourseInfo();
      await start(S.courseInfo);
      startBtn.disabled = false;
      singleBtn.disabled = false;
      stopBtn.disabled = true;
    });

    if (stopBtn) stopBtn.addEventListener('click', () => { stop(); startBtn.disabled = false; if(singleBtn) singleBtn.disabled = false; stopBtn.disabled = true; });
    if (txtBtn) txtBtn.addEventListener('click', downloadTxt);
    if (jsonBtn) jsonBtn.addEventListener('click', downloadJson);
    if (mdBtn) mdBtn.addEventListener('click', downloadMarkdown);
    if (xlsxBtn) xlsxBtn.addEventListener('click', downloadXlsx);
    if (copyBtn) copyBtn.addEventListener('click', copyText);

    // 折叠
    let collapsed = false;
    document.getElementById('cx-collapse').addEventListener('click', () => {
      collapsed = !collapsed;
      document.getElementById('cx-body').classList.toggle('cx-hidden', collapsed);
      panel.classList.toggle('cx-collapsed', collapsed);
      document.getElementById('cx-collapse').textContent = collapsed ? '+' : '−';
    });

    // 拖动
    makeDraggable(panel, document.getElementById('cx-head'));
  }

  function makeDraggable(p, h) {
    let sx, sy, ox, oy;
    h.addEventListener('mousedown', e => {
      sx = e.clientX; sy = e.clientY;
      const r = p.getBoundingClientRect();
      ox = r.left; oy = r.top;
      const mv = e2 => { p.style.right = 'auto'; p.style.top = 'auto'; p.style.left = (ox + e2.clientX - sx) + 'px'; p.style.top = (oy + e2.clientY - sy) + 'px'; };
      const up = () => { document.removeEventListener('mousemove', mv); document.removeEventListener('mouseup', up); };
      document.addEventListener('mousemove', mv);
      document.addEventListener('mouseup', up);
    });
  }

  function upProgress(text, pct) {
    if (pbar) pbar.style.width = pct + '%';
    const pt = document.getElementById('cx-ptext');
    if (pt) pt.textContent = text;
  }

  function upStatus(text, type) {
    if (statusEl) { statusEl.textContent = text; statusEl.className = 'cx-s ' + (type || 'info'); }
  }

  function enableBtns() {
    [txtBtn, copyBtn, jsonBtn, mdBtn, xlsxBtn].forEach(b => { if (b) b.disabled = false; });
  }

  function toast(msg) {
    const el = document.createElement('div');
    el.className = 'cx-toast'; el.textContent = msg;
    document.body.appendChild(el);
    setTimeout(() => el.remove(), 2200);
  }

  // ===================== 入口 =====================
  function init() {
    // 在iframe内：作为中继，转发来自更深层iframe的消息到顶层
    if (window.top !== window.self) {
      // 监听来自更深层iframe的提取结果并转发
      window.addEventListener('message', function (e) {
        if (e.data && e.data.type === 'CX_EXTRACT_RESULT' && e.data.questions?.length > 0) {
          log('[iframe中继] 转发', e.data.questions.length, '题到顶层');
          window.top.postMessage(e.data, '*');
        }
      });

      log('在iframe内，URL:', location.href.substring(0, 100));

      // 重试提取（题目可能通过JS延迟加载）
      let retries = 0;
      const maxRetries = 8;
      const tryExtract = () => {
        retries++;
        // 调试：列出页面上所有可能相关的元素
        const docEls = {
          TiMu: document.querySelectorAll('.TiMu').length,
          questionLi: document.querySelectorAll('.questionLi').length,
          questionItem: document.querySelectorAll('.question-item').length,
          mark_question: document.querySelectorAll('.mark_question').length,
          allDivs: document.querySelectorAll('div').length,
          bodyHTML: document.body ? document.body.innerHTML.substring(0, 500) : 'no body',
        };
        log(`[iframe内部-尝试${retries}] TiMu:${docEls.TiMu} qLi:${docEls.questionLi} qItem:${docEls.questionItem} mQ:${docEls.mark_question} divs:${docEls.allDivs}`);
        log(`[iframe内部-尝试${retries}] body前500字符:`, docEls.bodyHTML);
        const qs = extractQuestions(document);
        log(`[iframe内部-尝试${retries}] ${qs.length}题`);

        if (qs.length > 0) {
          log(`[iframe内部] 成功提取 ${qs.length} 题，发送给父页面`);
          window.top.postMessage({ type: 'CX_EXTRACT_RESULT', questions: qs, url: location.href }, '*');
          return;
        }

        // 也检查嵌套iframe
        const subIframes = document.querySelectorAll('iframe');
        for (const sif of subIframes) {
          try {
            const sdoc = sif.contentDocument || sif.contentWindow.document;
            if (sdoc?.body) {
              const innerQs = extractQuestions(sdoc);
              if (innerQs.length > 0) {
                log(`[iframe内部-嵌套] 提取到 ${innerQs.length} 题`);
                window.parent.postMessage({ type: 'CX_EXTRACT_RESULT', questions: innerQs, url: location.href }, '*');
                return;
              }
            }
          } catch (e) { /* sandbox */ }
        }

        // 再等等重试
        if (retries < maxRetries) {
          setTimeout(tryExtract, 1500);
        } else {
          log('[iframe内部] 达到最大重试次数，放弃');
          // 发送空结果通知父页面不需要再等
          window.parent.postMessage({ type: 'CX_EXTRACT_RESULT', questions: [], url: location.href }, '*');
        }
      };

      // 初始延迟后开始重试
      setTimeout(tryExtract, 2000);
      return;
    }

    const ci = getCourseInfo();

    // 检测页面类型
    const url = location.href;
    const isHome = /mooc2-ans\/mycourse\/stu\?/i.test(url); // 精确匹配stu?避免匹配studentcourse
    const isCardPage = /knowledge\/cards/i.test(url);
    const isStudyPage = /studentstudy/i.test(url);
    const isWorkPage = /selectWorkQuestion/i.test(url);

    if (isHome) {
      // 课程主页：需要 courseId，等待iframe
      S.courseInfo = ci;
      if (!ci.courseId) { log('非课程页面（无courseId）'); return; }
      let tries = 0;
      const waitIframe = () => {
        const iframe = document.getElementById('frame_content-zj');
        if (iframe || tries > 20) {
          createUI();
          const nameEl = document.getElementById('cx-cname');
          if (nameEl) nameEl.textContent = ci.name || '未检测到课程名';
          const cntEl = document.getElementById('cx-ccount');
          if (cntEl) cntEl.textContent = '等待提取...';
          upStatus('在课程主页，点击「▶ 自动提取全部」扫描所有章节测验，\n或先进入某个章节测验页面点击「📄 提取当前页」。', 'info');
        } else {
          tries++;
          setTimeout(waitIframe, 300);
        }
      };
      setTimeout(waitIframe, 1000);
    } else if (isCardPage || isStudyPage || isWorkPage) {
      // 章节测验/学习页面：可直接提取当前页
      S.courseInfo = ci;
      createUI();
      const nameEl = document.getElementById('cx-cname');
      if (nameEl) nameEl.textContent = ci.name || '当前章节';
      const cntEl = document.getElementById('cx-ccount');
      if (cntEl) cntEl.textContent = '直接提取';
      // 自动提取全部按钮在非主页隐藏
      if (startBtn) startBtn.style.display = 'none';
      upStatus('在章节测试页面，点击「📄 提取当前页」提取本页题目。\n回到课程主页可使用「自动提取全部」功能。', 'info');
    } else {
      log('不支持的页面类型: ' + url);
    }
  }

  if (document.readyState === 'complete') init();
  else window.addEventListener('load', () => setTimeout(init, 800));

})();

// Generate the small static project website. SPDX-License-Identifier: Apache-2.0
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath, pathToFileURL} from 'node:url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const args = process.argv.slice(2);
if (args.includes('--help')) {
  console.log('node tools/build-site.mjs --marked-module .tools/site/node_modules/marked/lib/marked.esm.js');
  process.exit(0);
}
if (args.length !== 2 || args[0] !== '--marked-module') throw Error('Use --help for the build command');
const markedPath = path.resolve(args[1]);
const metadata = JSON.parse(fs.readFileSync(path.resolve(path.dirname(markedPath), '../package.json'), 'utf8'));
if (metadata.name !== 'marked' || metadata.version !== '17.0.5') throw Error('Use marked 17.0.5');
const {Marked} = await import(pathToFileURL(markedPath).href);
const out = path.join(root, 'docs');
fs.mkdirSync(out, {recursive:true});
const pages = new Map([
  ['README.md', 'index.html'], ['MAIN-STATEMENTS.md', 'main-statements.html'],
  ['CONSISTENCY.md', 'consistency.html'],
  ['lean/ReyZygmund/MathlibOnly/README.md', 'mathlib-only.html'],
  ['VERIFYING.md', 'verifying.html'], ['verification/LINUX-SETUP.md', 'linux-setup.html'],
  ['verification/PACKAGING-TESTS.md', 'packaging-tests.html'],
  ['lean/THIRD_PARTY.md', 'third-party.html'], ['SITE.md', 'site.html']
]);
const escape = s => s.replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;').replaceAll('"', '&quot;');
const slug = s => s.toLowerCase().replace(/<[^>]*>/g, '').replace(/[^\p{L}\p{N}\s_-]/gu, '').trim().replace(/\s/g, '-');
const css = `:root{color-scheme:light;--ink:#202c35;--muted:#52626e;--link:#176577;--rule:#dce3e6}
*{box-sizing:border-box}html{scroll-behavior:smooth;scroll-padding-top:2rem}body{margin:0;color:var(--ink);background:#fff;font:17px/1.7 Georgia,'Times New Roman',serif}
a{color:var(--link);text-underline-offset:.18em}a:hover{color:#103f4c}a:focus-visible{outline:2px solid var(--link);outline-offset:4px}
header,main,footer{max-width:940px;margin:auto;padding:0 28px}header{padding-top:26px;padding-bottom:20px;border-bottom:1px solid var(--rule);font:14px/1.8 system-ui,sans-serif}
nav{display:flex;gap:22px;flex-wrap:wrap}nav a{text-decoration:none}main{padding-top:36px;padding-bottom:50px}h1,h2,h3{line-height:1.25;font-weight:normal;color:#182a35}
h1{font-size:2.35rem;margin:0 0 1.3rem;letter-spacing:-.025em}h2{font-size:1.55rem;margin:2.25rem 0 1rem;padding-top:.15rem}h3{font-size:1.18rem;margin-top:1.8rem}
p{margin:1rem 0}ul,ol{padding-left:1.5rem}li{margin:.35rem 0}strong{font-weight:600}code{font: .86em/1.5 ui-monospace,SFMono-Regular,Consolas,monospace;overflow-wrap:anywhere}
pre{background:#f5f7f8;padding:18px 20px;border:1px solid var(--rule);border-radius:4px;overflow:auto;line-height:1.5}pre code{overflow-wrap:normal}
table{width:100%;border-collapse:collapse;font-size:.91em;margin:1.4rem 0}th{text-align:left;font-weight:600;background:#f7f9fa}td,th{padding:10px 12px;vertical-align:top;border-bottom:1px solid var(--rule)}
blockquote{margin:1.5rem 0;border-left:3px solid var(--rule);padding-left:1.2rem;color:var(--muted)}footer{border-top:1px solid var(--rule);padding-top:20px;padding-bottom:35px;color:var(--muted);font:13px/1.8 system-ui,sans-serif}
.math-display{overflow-x:auto;padding:.3rem 0}.source{max-width:none;font-size:13px}.source .line{display:block;min-height:1.5em}.source .line:target{background:#fff2bc}.source .number{display:inline-block;width:4em;padding-right:1em;text-align:right;color:#6b7780;text-decoration:none;user-select:none}
@media(max-width:600px){body{font-size:16px}header,main,footer{padding-left:18px;padding-right:18px}h1{font-size:1.9rem}nav{gap:14px}td,th{padding:8px 6px}table{font-size:.8em}pre{padding:12px}}
@media print{nav{display:none}body{font-size:11pt}a{color:inherit;text-decoration:none}pre,table{break-inside:avoid}}`;
fs.writeFileSync(path.join(out, 'style.css'), css + '\n');
const shell = (title, content, prefix='') => `<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>${escape(title)} · Zygmund and Rey in Lean</title>
<meta name="description" content="Lean 4 formalization of proofs of the Zygmund conjecture and Rey’s exponential integrability conjecture, with theorem statements and reproducible verification.">
<link rel="stylesheet" href="${prefix}style.css">
<script>window.MathJax={tex:{inlineMath:[['\\\\(','\\\\)']],displayMath:[['\\\\[','\\\\]']]},svg:{fontCache:'local'},options:{skipHtmlTags:['script','noscript','style','textarea','pre','code']}};</script>
<script defer src="https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-svg.js"></script>
</head><body><header><nav aria-label="Main navigation">
<a href="${prefix}index.html">Overview</a><a href="${prefix}main-statements.html">Main theorems</a>
<a href="${prefix}consistency.html">Definitions and consistency</a>
<a href="${prefix}verifying.html">Verification</a><a href="https://arxiv.org/abs/2609.23895">Paper ↗</a>
</nav></header><main>${content}</main><footer>Henri Martikainen · Lean 4 and Mathlib · <a href="${prefix}third-party.html">Apache-2.0 &amp; acknowledgments</a></footer></body></html>\n`;

const inventory = JSON.parse(fs.readFileSync(path.join(root, 'verification/SOURCE-MANIFEST.json'), 'utf8')).sha256;
const copied = new Set();
function localLink(href, from) {
  if (/^(https?:|mailto:|#)/.test(href)) return href;
  const [raw, fragment=''] = href.split('#');
  const relative = path.posix.normalize(path.posix.join(path.posix.dirname(from), raw));
  if (relative.startsWith('../') || path.isAbsolute(relative)) throw Error('Escaping link: ' + href);
  if (!fs.existsSync(path.join(root, relative))) throw Error('Missing link: ' + relative);
  let target;
  if (pages.has(relative)) target = pages.get(relative);
  else if (Object.hasOwn(inventory, relative)) target = 'source/' + relative + '.html';
  else {
    target = 'files/' + relative;
    if (!copied.has(relative)) {
      const dest = path.join(out, target);
      fs.mkdirSync(path.dirname(dest), {recursive:true});
      fs.copyFileSync(path.join(root, relative), dest);
      copied.add(relative);
    }
  }
  return target + (fragment ? '#' + fragment : '');
}

for (const [source, destination] of pages) {
  const equations = [];
  let text = fs.readFileSync(path.join(root, source), 'utf8');
  // Protect GitHub's math fences and inline delimiters before parsing Markdown.
  // Ordinary code fences/spans stay literal; legacy dollar math is still supported.
  text = text.replace(
    /^```([^\n]*)\n([\s\S]*?)^```[ \t]*$|\$\$([\s\S]*?)\$\$|\$`([^`\n]+)`\$|(`[^`\n]*`)|\$([^$\n]+)\$/gm,
    (whole, language, fenced, legacyDisplay, protectedInline, code, inline) => {
      if (language !== undefined && language.trim() !== 'math' || code !== undefined) return whole;
      const display = fenced !== undefined || legacyDisplay !== undefined;
      const value = fenced ?? legacyDisplay ?? protectedInline ?? inline;
      const id = equations.length;
      equations.push({value, display});
      return display ? `\n\nRZMATH${id}END\n\n` : `RZMATH${id}END`;
    }
  );
  const parser = new Marked({gfm:true, renderer:{
    heading(token) {const content=this.parser.parseInline(token.tokens); return `<h${token.depth} id="${slug(token.text)}">${content}</h${token.depth}>\n`;},
    link(token) {return `<a href="${escape(localLink(token.href, source))}">${this.parser.parseInline(token.tokens)}</a>`;}
  }});
  let html = parser.parse(text);
  equations.forEach(({value, display}, i) => {
    const token = `RZMATH${i}END`;
    if (display) html = html.replace(`<p>${token}</p>`, `<div class="math-display">\\[${escape(value.trim())}\\]</div>`);
    else html = html.replaceAll(token, `<span class="math-inline">\\(${escape(value)}\\)</span>`);
  });
  if (/RZMATH\d+END/.test(html)) throw Error('Unrendered math placeholder');
  const title = fs.readFileSync(path.join(root, source), 'utf8').match(/^# (.+)$/m)[1];
  fs.writeFileSync(path.join(out, destination), shell(title, html));
}
for (const relative of Object.keys(inventory)) {
  const filename = 'source/' + relative + '.html';
  const destination = path.join(out, filename);
  const depth = path.posix.dirname(filename).split('/').length;
  const lines = fs.readFileSync(path.join(root, relative), 'utf8').split('\n');
  const html = lines.map((s,i) => `<span class="line" id="L${i+1}"><a class="number" href="#L${i+1}">${i+1}</a>${escape(s)}</span>`).join('');
  fs.mkdirSync(path.dirname(destination), {recursive:true});
  fs.writeFileSync(destination, shell(relative, `<h1>${escape(relative)}</h1><pre class="source"><code>${html}</code></pre>`, '../'.repeat(depth)));
}
fs.writeFileSync(path.join(out, '.nojekyll'), '');
console.log(`Built ${pages.size} pages and ${Object.keys(inventory).length} source views in docs/. No publishing performed.`);

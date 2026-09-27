# Building and maintaining the website

These instructions explain how to preview and rebuild the optional website
from the repository's Markdown and Lean files. The generated pages in `docs/`
present the mathematical statements, consistency explanations, verification
instructions and browsable Lean sources.

For a local preview from the repository root:

```sh
python3 -m http.server 8000 --bind 127.0.0.1 --directory docs
```

Then open `http://127.0.0.1:8000`. Math rendering uses the pinned MathJax 3.2.2
script from jsDelivr; opening a page with network access therefore requests that
script from the jsDelivr CDN. The text and source pages remain readable without it.
No analytics, cookies or external fonts are added by the site itself.

The HTML is generated from the Markdown documents and exact Lean source
inventory. Use GitHub's fenced `math` blocks for displayed equations and
dollar-and-backtick delimiters for inline math. The generator preserves the
same TeX expressions for the website.

To regenerate it after editorial changes, use Node.js 20+ and Marked 17.0.5:

```sh
npm install --prefix .tools/site --ignore-scripts --save-exact marked@17.0.5
node tools/build-site.mjs --marked-module .tools/site/node_modules/marked/lib/marked.esm.js
```

Marked is a build-time dependency and is not vendored. MathJax is loaded from
its public CDN, not copied into this repository. Their respective upstream
licenses remain applicable to those tools.

GitHub Pages can serve `docs/` from the chosen branch; `.nojekyll` keeps it a
plain static site. The repository README is also a complete landing page
without Pages.

See GitHub's [publishing-source instructions](https://docs.github.com/en/pages/getting-started-with-github-pages/configuring-a-publishing-source-for-your-github-pages-site).

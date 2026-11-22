// main.ts is mend, the CLI SPEC.md specifies. It does all ten sections: the command line, the output and
// exit codes, safe paths, format detection, three-tier line matching, unified diffs, SEARCH/REPLACE
// blocks, V4A patches, JSON edits and the all-or-nothing write. Node 22, the standard library alone;
// run it as `node main.ts [options] [PATCH]`.
//
// How it is built: every patch format is parsed first into a uniform list of edit records (one record
// per edit: its kind, its paths, and its chunks of old/new lines), before any file is touched. Each
// record then becomes one closure that applies against the tree. All three line formats share one
// occurrence finder (a sliding-window search returning every occurrence position, tried tier by tier)
// and one replacement builder (context lines are always written as the file's own matched lines, and
// at tier 2 the other new lines are re-indented from the old lines' leading whitespace to the file's).
// The per-format applicators differ only in how they pick an occurrence: a unified hunk takes the one
// nearest its header line, a SEARCH/REPLACE block demands exactly one, and a V4A chunk takes the first
// at or after its cursor (after its anchor, when it has one).
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands
// over to runner.ts (the last lines below): keep that hand-over and runner.ts as they are.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

/* ------------------------------------------------------------------ */
/* Lines, tiers and the shared occurrence finder (SPEC.md section 5)  */
/* ------------------------------------------------------------------ */

const trimEndWs = (s: string): string => s.replace(/[ \t]+$/, '');
const trimWs = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const leadWs = (s: string): string => {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
};
const onlyWs = (s: string): boolean => s === '' || /^[ \t]+$/.test(s);

function lineEq(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return trimEndWs(a) === trimEndWs(b);
  return trimWs(a) === trimWs(b);
}

/** Every 0-based position at which O occurs in `lines` at this tier, from `from` on. */
function occurrences(o: string[], lines: string[], tier: number, from = 0): number[] {
  const out: number[] = [];
  if (o.length === 0) return out;
  for (let i = from; i + o.length <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < o.length; j++) {
      if (!lineEq(o[j]!, lines[i + j]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/**
 * The first tier (0, then 1, then 2; only 0 when strict) at which O occurs at or after `from`,
 * with every occurrence position at that tier. For an end-of-file chunk only occurrences that end
 * at the file's last line count. Null when O occurs at no tier.
 */
function findTier(
  o: string[],
  lines: string[],
  strict: boolean,
  from = 0,
  eofOnly = false,
): { tier: number; pos: number[] } | null {
  const max = strict ? 0 : 2;
  for (let t = 0; t <= max; t++) {
    let pos = occurrences(o, lines, t, from);
    if (eofOnly) pos = pos.filter((p) => p + o.length === lines.length);
    if (pos.length > 0) return { tier: t, pos };
  }
  return null;
}

/** A file as lines: its own line break, and whether it ends with one. */
interface FFile {
  lines: string[];
  br: string;
  final: boolean;
}

function splitFile(text: string): FFile {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const fin = text.endsWith(br);
  if (fin) parts.pop();
  return { lines: parts, br, final: fin };
}

function joinFile(f: FFile): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.final ? f.br : '');
}

/**
 * The lines that replace a matched occurrence at `at`. A context line of N is written as the
 * file's own matched line, never the patch's; at tier 2 every other line of N that starts with
 * the leading whitespace P of O's first line has that P replaced by F, the leading whitespace
 * of the file's first matched line.
 */
function buildReplacement(
  o: string[],
  n: string[],
  oCtx: boolean[],
  nCtx: boolean[],
  lines: string[],
  at: number,
  tier: number,
): string[] {
  const oCtxIdx: number[] = [];
  oCtx.forEach((c, i) => {
    if (c) oCtxIdx.push(i);
  });
  const F = o.length > 0 ? leadWs(lines[at] ?? '') : '';
  const P = o.length > 0 ? leadWs(o[0]!) : '';
  const out: string[] = [];
  let ctxOrd = 0;
  for (let j = 0; j < n.length; j++) {
    if (nCtx[j]) {
      out.push(lines[at + oCtxIdx[ctxOrd]!]!);
      ctxOrd += 1;
    } else {
      let s = n[j]!;
      if (tier === 2 && !onlyWs(s) && s.startsWith(P)) s = F + s.slice(P.length);
      out.push(s);
    }
  }
  return out;
}

/* ------------------------------------------------------------------ */
/* Uniform internal edits: what every parser produces                 */
/* ------------------------------------------------------------------ */

interface Chunk {
  o: string[];
  n: string[];
  oCtx: boolean[];
  nCtx: boolean[];
  /** Unified hunk header's -A (insertion line); unused by the other modes. */
  a: number;
  /** A `\` line follows this chunk's last context or `+` line (unified final-break rule). */
  noNL: boolean;
  /** A `\` line follows this chunk's last `+` line (unified creation rule). */
  plusNoNL: boolean;
  /** V4A chunk anchor; null when the chunk has none. */
  anchor: string | null;
  /** V4A end-of-file chunk: the match must end at the file's last line. */
  eof: boolean;
  /** How the occurrence is picked: nearest (unified), cursor (V4A), once (SEARCH/REPLACE). */
  mode: 'nearest' | 'cursor' | 'once';
}

interface Rec {
  kind: 'create' | 'delete' | 'change' | 'move';
  /** The file the edit touches (the old path of a move). */
  path: string;
  /** The new path of a move; null otherwise. */
  newPath: string | null;
  /** Lines of a created file; null unless kind is 'create'. */
  createLines: string[] | null;
  /** Whether a created file ends with a line break. */
  createFinal: boolean;
  chunks: Chunk[];
  fmt: 'unified' | 'sr' | 'v4a';
}

const emptyChunk = (mode: Chunk['mode']): Chunk => ({
  o: [],
  n: [],
  oCtx: [],
  nCtx: [],
  a: 0,
  noNL: false,
  plusNoNL: false,
  anchor: null,
  eof: false,
  mode,
});

/** Apply a record's chunks, in order, to a file's lines. Throws Fail on the first bad chunk. */
function applyChunks(rec: Rec, f: FFile, strict: boolean): FFile {
  const lines = [...f.lines];
  let fin = f.final;
  let d = 0;
  let cursor = 0;
  for (const ch of rec.chunks) {
    if (ch.mode === 'nearest') {
      if (ch.o.length === 0) {
        let at = ch.a + d;
        if (at < 0) at = 0;
        if (at > lines.length) at = lines.length;
        const atEnd = at === lines.length;
        lines.splice(at, 0, ...ch.n);
        if (atEnd) fin = !ch.noNL;
      } else {
        const found = findTier(ch.o, lines, strict, 0);
        if (found === null) throw new Fail('no-match', rec.path);
        const target = ch.a - 1 + d;
        let best = found.pos[0]!;
        for (const p of found.pos) {
          if (Math.abs(p - target) < Math.abs(best - target)) best = p;
        }
        const runsToEnd = best + ch.o.length === lines.length;
        const rep = buildReplacement(ch.o, ch.n, ch.oCtx, ch.nCtx, lines, best, found.tier);
        lines.splice(best, ch.o.length, ...rep);
        if (runsToEnd) fin = !ch.noNL;
      }
      d += ch.n.length - ch.o.length;
    } else if (ch.mode === 'cursor') {
      if (ch.anchor !== null) {
        const found = findTier([ch.anchor], lines, strict, cursor);
        if (found === null) throw new Fail('no-match', rec.path);
        cursor = found.pos[0]! + 1;
      }
      if (ch.o.length === 0) {
        let at = ch.eof ? lines.length : cursor;
        if (at > lines.length) at = lines.length;
        lines.splice(at, 0, ...ch.n);
        cursor = at + ch.n.length;
      } else {
        const found = findTier(ch.o, lines, strict, cursor, ch.eof);
        if (found === null) throw new Fail('no-match', rec.path);
        const at = found.pos[0]!;
        const rep = buildReplacement(ch.o, ch.n, ch.oCtx, ch.nCtx, lines, at, found.tier);
        lines.splice(at, ch.o.length, ...rep);
        cursor = at + rep.length;
      }
    } else {
      const found = findTier(ch.o, lines, strict, 0);
      if (found === null) throw new Fail('no-match', rec.path);
      if (found.pos.length > 1) throw new Fail('ambiguous', rec.path);
      const at = found.pos[0]!;
      const rep = buildReplacement(ch.o, ch.n, ch.oCtx, ch.nCtx, lines, at, found.tier);
      lines.splice(at, ch.o.length, ...rep);
    }
  }
  return { lines, br: f.br, final: fin };
}

/** One uniform record as an edit against the tree. Safety first, then missing/exists, then match. */
function recToEdit(rec: Rec, strict: boolean, moves: Array<{ old: string; new: string }>): Edit {
  return (tree) => {
    if (!safe(rec.path)) throw new Fail('unsafe', rec.path);
    if (rec.newPath !== null && !safe(rec.newPath)) throw new Fail('unsafe', rec.newPath);
    if (rec.kind === 'create') {
      if (tree.get(rec.path) !== null) throw new Fail('exists', rec.path);
      const ls = rec.createLines ?? [];
      tree.now.set(rec.path, ls.length === 0 ? '' : ls.join('\n') + (rec.createFinal ? '\n' : ''));
      return;
    }
    if (rec.kind === 'delete') {
      if (tree.get(rec.path) === null) throw new Fail('missing', rec.path);
      tree.now.set(rec.path, null);
      return;
    }
    const before = tree.get(rec.path);
    if (before === null) throw new Fail('missing', rec.path);
    if (rec.kind === 'move' && rec.newPath !== null && tree.get(rec.newPath) !== null) {
      throw new Fail('exists', rec.newPath);
    }
    const out = applyChunks(rec, splitFile(before), strict);
    const text = joinFile(out);
    if (rec.kind === 'move' && rec.newPath !== null) {
      tree.now.set(rec.newPath, text);
      tree.now.set(rec.path, null);
      moves.push({ old: rec.path, new: rec.newPath });
    } else {
      tree.now.set(rec.path, text);
    }
  };
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/* ------------------------------------------------------------------ */
/* Unified diffs (SPEC.md section 6)                                  */
/* ------------------------------------------------------------------ */

interface USection {
  diffOld: string | null;
  diffNew: string | null;
  hdrOld: string | null;
  hdrNew: string | null;
  renameFrom: string | null;
  renameTo: string | null;
  newFileMode: boolean;
  deletedFileMode: boolean;
  hunks: Chunk[];
}

/** The path of a `--- ` / `+++ ` line: after the four characters, up to the first tab, trimmed. */
function headerPath(line: string): string {
  const rest = line.slice(4);
  const tab = rest.indexOf('\t');
  return (tab >= 0 ? rest.slice(0, tab) : rest).trim();
}

/** A leading `a/` or `b/` is removed from a `--- ` / `+++ ` path. */
function stripAB(p: string): string {
  return p.startsWith('a/') || p.startsWith('b/') ? p.slice(2) : p;
}

type BodyLine = { t: ' ' | '-' | '+' | '\\'; text: string; raw: string };

function bodyLine(l: string): BodyLine {
  if (l === '') return { t: ' ', text: '', raw: l };
  if (l[0] === ' ') return { t: ' ', text: l.slice(1), raw: l };
  if (l[0] === '-') return { t: '-', text: l.slice(1), raw: l };
  if (l[0] === '+') return { t: '+', text: l.slice(1), raw: l };
  return { t: '\\', text: l.slice(1), raw: l };
}

function hunkFromBody(a: number, body: BodyLine[]): Chunk {
  const ch = emptyChunk('nearest');
  ch.a = a;
  let lastCtxPlus = -1;
  let lastPlus = -1;
  body.forEach((e, idx) => {
    if (e.t === ' ') {
      ch.o.push(e.text);
      ch.oCtx.push(true);
      ch.n.push(e.text);
      ch.nCtx.push(true);
      lastCtxPlus = idx;
    } else if (e.t === '-') {
      ch.o.push(e.text);
      ch.oCtx.push(false);
    } else if (e.t === '+') {
      ch.n.push(e.text);
      ch.nCtx.push(false);
      lastCtxPlus = idx;
      lastPlus = idx;
    }
  });
  ch.noNL = lastCtxPlus >= 0 && lastCtxPlus + 1 < body.length && body[lastCtxPlus + 1]!.t === '\\';
  ch.plusNoNL = lastPlus >= 0 && lastPlus + 1 < body.length && body[lastPlus + 1]!.t === '\\';
  return ch;
}

function sectionToRec(s: USection): Rec {
  const oldP = s.hdrOld ?? s.renameFrom ?? s.diffOld;
  const newP = s.hdrNew ?? s.renameTo ?? s.diffNew;
  const oldNull = oldP === '/dev/null';
  const newNull = newP === '/dev/null';
  const oldPath = oldNull ? null : oldP;
  const newPath = newNull ? null : newP;
  if (oldNull || s.newFileMode) {
    const plus: string[] = [];
    for (const h of s.hunks) {
      h.n.forEach((t, j) => {
        if (!h.nCtx[j]) plus.push(t);
      });
    }
    let final = true;
    for (let k = s.hunks.length - 1; k >= 0; k--) {
      const h = s.hunks[k]!;
      if (h.n.some((_, j) => !h.nCtx[j])) {
        final = !h.plusNoNL;
        break;
      }
    }
    return { kind: 'create', path: newPath ?? '', newPath: null, createLines: plus, createFinal: final, chunks: [], fmt: 'unified' };
  }
  if (newNull || s.deletedFileMode) {
    return { kind: 'delete', path: oldPath ?? '', newPath: null, createLines: null, createFinal: true, chunks: [], fmt: 'unified' };
  }
  if (oldPath !== newPath) {
    return { kind: 'move', path: oldPath ?? '', newPath: newPath ?? '', createLines: null, createFinal: true, chunks: s.hunks, fmt: 'unified' };
  }
  return { kind: 'change', path: oldPath ?? '', newPath: null, createLines: null, createFinal: true, chunks: s.hunks, fmt: 'unified' };
}

function unifiedEdits(lines: string[]): Rec[] {
  const sections: USection[] = [];
  let cur: USection | null = null;
  let inHeader = false;
  let headerPairSeen = false;
  const startSection = (s: USection, pairSeen: boolean): void => {
    sections.push(s);
    cur = s;
    inHeader = true;
    headerPairSeen = pairSeen;
  };
  const blankSection = (): USection => ({
    diffOld: null,
    diffNew: null,
    hdrOld: null,
    hdrNew: null,
    renameFrom: null,
    renameTo: null,
    newFileMode: false,
    deletedFileMode: false,
    hunks: [],
  });
  let i = 0;
  while (i < lines.length) {
    const l = lines[i]!;
    if (l.startsWith('diff --git ')) {
      const m = /^diff --git a\/(\S+) b\/(\S+)[ \t]*$/.exec(l);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      const s = blankSection();
      s.diffOld = m[1]!;
      s.diffNew = m[2]!;
      startSection(s, false);
      i++;
      continue;
    }
    if (l.startsWith('--- ')) {
      const nxt = lines[i + 1];
      if (nxt !== undefined && nxt.startsWith('+++ ')) {
        if (cur !== null && inHeader && !headerPairSeen) {
          cur.hdrOld = stripAB(headerPath(l));
          cur.hdrNew = stripAB(headerPath(nxt));
          headerPairSeen = true;
          i += 2;
          continue;
        }
        const s = blankSection();
        s.hdrOld = stripAB(headerPath(l));
        s.hdrNew = stripAB(headerPath(nxt));
        startSection(s, true);
        i += 2;
        continue;
      }
      if (cur !== null && inHeader) throw new Exit2(`error: parse ${i + 2}`);
      i++;
      continue;
    }
    if (l.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@(?:[ \t].*)?$/.exec(l);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      const a = parseInt(m[1]!, 10);
      const body: BodyLine[] = [];
      let j = i + 1;
      while (j < lines.length) {
        const bl = lines[j]!;
        if (bl.startsWith('diff --git ')) break;
        if (bl.startsWith('--- ') && lines[j + 1] !== undefined && lines[j + 1]!.startsWith('+++ ')) break;
        if (bl === '' || bl.startsWith(' ') || bl.startsWith('-') || bl.startsWith('+') || bl.startsWith('\\')) {
          body.push(bodyLine(bl));
          j++;
          continue;
        }
        break;
      }
      while (body.length > 0 && body[body.length - 1]!.raw === '') body.pop();
      cur.hunks.push(hunkFromBody(a, body));
      inHeader = false;
      i = j;
      continue;
    }
    if (cur !== null && inHeader) {
      if (l.startsWith('rename from ')) cur.renameFrom = l.slice('rename from '.length).trim();
      else if (l.startsWith('rename to ')) cur.renameTo = l.slice('rename to '.length).trim();
      else if (l === 'new file mode' || l.startsWith('new file mode ')) cur.newFileMode = true;
      else if (l === 'deleted file mode' || l.startsWith('deleted file mode ')) cur.deletedFileMode = true;
      i++;
      continue;
    }
    i++;
  }
  return sections.map(sectionToRec);
}

/* ------------------------------------------------------------------ */
/* SEARCH/REPLACE blocks (SPEC.md section 7)                          */
/* ------------------------------------------------------------------ */

function srEdits(lines: string[]): Rec[] {
  const recs: Rec[] = [];
  let i = 0;
  let prevEnd = -1;
  let prevPath: string | null = null;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() === '<<<<<<< SEARCH') {
      const searchLine = i + 1;
      let path: string | null = null;
      for (let j = i - 1; j > prevEnd; j--) {
        const l = lines[j]!;
        if (blank(l)) continue;
        if (l.trim().startsWith('```')) continue;
        path = l.trim();
        break;
      }
      if (path === null) {
        if (prevPath === null) throw new Exit2(`error: parse ${searchLine}`);
        path = prevPath;
      }
      const oldLines: string[] = [];
      let j = i + 1;
      let foundEq = false;
      while (j < lines.length) {
        const l = lines[j]!;
        if (l.trimEnd() === '<<<<<<< SEARCH') break;
        if (l.trimEnd() === '=======') {
          foundEq = true;
          break;
        }
        oldLines.push(l);
        j++;
      }
      if (!foundEq) throw new Exit2(`error: parse ${searchLine}`);
      const newLines: string[] = [];
      j++;
      let foundEnd = false;
      while (j < lines.length) {
        const l = lines[j]!;
        if (l.trimEnd() === '<<<<<<< SEARCH') break;
        if (l.trimEnd() === '>>>>>>> REPLACE') {
          foundEnd = true;
          break;
        }
        newLines.push(l);
        j++;
      }
      if (!foundEnd) throw new Exit2(`error: parse ${searchLine}`);
      prevEnd = j;
      prevPath = path;
      if (oldLines.length === 0) {
        recs.push({ kind: 'create', path, newPath: null, createLines: newLines, createFinal: true, chunks: [], fmt: 'sr' });
      } else {
        const ch = emptyChunk('once');
        ch.o = oldLines;
        ch.n = newLines;
        ch.oCtx = oldLines.map(() => false);
        ch.nCtx = newLines.map(() => false);
        recs.push({ kind: 'change', path, newPath: null, createLines: null, createFinal: true, chunks: [ch], fmt: 'sr' });
      }
      i = j + 1;
    } else {
      i++;
    }
  }
  return recs;
}

/* ------------------------------------------------------------------ */
/* V4A patches (SPEC.md section 8)                                    */
/* ------------------------------------------------------------------ */

const V4A_STARTS = ['*** Add File: ', '*** Delete File: ', '*** Update File: '];
const isV4ASectionStart = (l: string): boolean => V4A_STARTS.some((p) => l.startsWith(p));

interface VChunkWork {
  o: string[];
  n: string[];
  oCtx: boolean[];
  nCtx: boolean[];
  anchor: string | null;
  eof: boolean;
}

function v4aSection(lines: string[], start: number, end: number): Rec {
  const head = lines[start]!;
  const kind = head.startsWith('*** Add File: ') ? 'add' : head.startsWith('*** Delete File: ') ? 'delete' : 'update';
  const prefixLen = kind === 'add' ? '*** Add File: '.length : kind === 'delete' ? '*** Delete File: '.length : '*** Update File: '.length;
  const path = head.slice(prefixLen).trim();
  let rawEnd = end;
  while (rawEnd > start + 1 && blank(lines[rawEnd - 1]!)) rawEnd--;
  const raw = lines.slice(start + 1, rawEnd);
  if (kind === 'add') {
    const content: string[] = [];
    for (let k = 0; k < raw.length; k++) {
      const l = raw[k]!;
      if (l === '') content.push('');
      else if (l.startsWith('+')) content.push(l.slice(1));
      else throw new Exit2(`error: parse ${start + 2 + k}`);
    }
    return { kind: 'create', path, newPath: null, createLines: content, createFinal: true, chunks: [], fmt: 'v4a' };
  }
  if (kind === 'delete') {
    for (let k = 0; k < raw.length; k++) {
      if (!blank(raw[k]!)) throw new Exit2(`error: parse ${start + 2 + k}`);
    }
    return { kind: 'delete', path, newPath: null, createLines: null, createFinal: true, chunks: [], fmt: 'v4a' };
  }
  let newPath: string | null = null;
  let at = 0;
  if (raw.length > 0 && raw[0]!.startsWith('*** Move to: ')) {
    newPath = raw[0]!.slice('*** Move to: '.length).trim();
    at = 1;
  }
  const chunks: Chunk[] = [];
  let cur: VChunkWork | null = null;
  let haveChunk = false;
  const closeChunk = (): void => {
    if (cur === null) return;
    const ch = emptyChunk('cursor');
    ch.o = cur.o;
    ch.n = cur.n;
    ch.oCtx = cur.oCtx;
    ch.nCtx = cur.nCtx;
    ch.anchor = cur.anchor;
    ch.eof = cur.eof;
    chunks.push(ch);
    cur = null;
  };
  for (let k = at; k < raw.length; k++) {
    const l = raw[k]!;
    const lineNo = start + 2 + k;
    if (l.trimEnd() === '*** End of File') {
      if (cur === null) throw new Exit2(`error: parse ${lineNo}`);
      cur.eof = true;
      closeChunk();
      continue;
    }
    if (l.startsWith('@@')) {
      closeChunk();
      cur = { o: [], n: [], oCtx: [], nCtx: [], anchor: l.slice(2).trim(), eof: false };
      haveChunk = true;
      continue;
    }
    if (l === '' || l.startsWith(' ') || l.startsWith('-') || l.startsWith('+')) {
      if (cur === null) {
        if (!haveChunk) {
          cur = { o: [], n: [], oCtx: [], nCtx: [], anchor: null, eof: false };
          haveChunk = true;
        } else {
          throw new Exit2(`error: parse ${lineNo}`);
        }
      }
      if (l === '') {
        cur.o.push('');
        cur.oCtx.push(true);
        cur.n.push('');
        cur.nCtx.push(true);
      } else if (l.startsWith(' ')) {
        const t = l.slice(1);
        cur.o.push(t);
        cur.oCtx.push(true);
        cur.n.push(t);
        cur.nCtx.push(true);
      } else if (l.startsWith('-')) {
        cur.o.push(l.slice(1));
        cur.oCtx.push(false);
      } else {
        cur.n.push(l.slice(1));
        cur.nCtx.push(false);
      }
      continue;
    }
    throw new Exit2(`error: parse ${lineNo}`);
  }
  closeChunk();
  if (chunks.length === 0 && newPath === null) throw new Exit2(`error: parse ${start + 1}`);
  if (newPath !== null) {
    return { kind: 'move', path, newPath, createLines: null, createFinal: true, chunks, fmt: 'v4a' };
  }
  return { kind: 'change', path, newPath: null, createLines: null, createFinal: true, chunks, fmt: 'v4a' };
}

function v4aEdits(lines: string[]): Rec[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = lines.length - 1;
  while (last >= 0 && blank(lines[last]!)) last--;
  if (last < 0 || lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const recs: Rec[] = [];
  let i = first + 1;
  while (i < last) {
    const l = lines[i]!;
    if (blank(l)) {
      i++;
      continue;
    }
    if (!isV4ASectionStart(l)) throw new Exit2(`error: parse ${i + 1}`);
    let j = i + 1;
    while (j < last && !isV4ASectionStart(lines[j]!)) j++;
    recs.push(v4aSection(lines, i, j));
    i = j;
  }
  return recs;
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  const moves: Array<{ old: string; new: string }> = [];
  try {
    if (kind === 'json') {
      edits = jsonEdits(text, lines);
    } else {
      const recs: Rec[] =
        kind === 'unified' ? unifiedEdits(lines) : kind === 'search-replace' ? srEdits(lines) : v4aEdits(lines);
      edits = recs.map((r) => recToEdit(r, strict, moves));
    }
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const changed = new Map<string, { was: string | null; now: string | null }>();
  for (const p of tree.now.keys()) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was !== now) changed.set(p, { was, now });
  }
  const usedOld = new Set<string>();
  const usedNew = new Set<string>();
  const rows: { key: string; text: string }[] = [];
  for (const m of moves) {
    const oc = changed.get(m.old);
    const nc = changed.get(m.new);
    if (
      oc !== undefined &&
      nc !== undefined &&
      oc.was !== null &&
      oc.now === null &&
      nc.was === null &&
      nc.now !== null &&
      !usedOld.has(m.old) &&
      !usedNew.has(m.new)
    ) {
      rows.push({ key: m.new, text: `R ${m.old} -> ${m.new}` });
      usedOld.add(m.old);
      usedNew.add(m.new);
    }
  }
  for (const [p, c] of changed) {
    if (usedOld.has(p) || usedNew.has(p)) continue;
    rows.push({ key: p, text: `${c.was === null ? 'A' : c.now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  if (!check) {
    for (const [p, c] of changed) {
      if (c.now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, c.now);
      }
    }
  }
  return { code: 0, out: [...rows.map((r) => r.text), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}

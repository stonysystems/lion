#!/usr/bin/env python3
"""
Count lines of Verus/Rust code by category:
  1. Exec     — verified executable code inside verus! blocks
  2. Spec     — spec fns, proof fns, contracts (requires/ensures), assertions
  3. Trusted  — external_body/external fn bodies inside verus! blocks (TCB)
  4. Adapter  — code outside verus! blocks in files marked verus::trusted
  5. Wrapper  — code outside verus! blocks in unmarked files

Usage: python3 count_lines.py <directory> [--verbose] [--spec-only]
"""

import sys
import os
import re

class FileStats:
    def __init__(self, path):
        self.path = path
        self.exec_lines = 0
        self.spec_proof_lines = 0
        self.trusted_lines = 0
        self.adapter_lines = 0
        self.wrapper_lines = 0

class Stats:
    def __init__(self):
        self.exec_lines = 0
        self.spec_proof_lines = 0
        self.trusted_lines = 0
        self.adapter_lines = 0
        self.wrapper_lines = 0
        self.files = []

    def add(self, fs):
        self.exec_lines += fs.exec_lines
        self.spec_proof_lines += fs.spec_proof_lines
        self.trusted_lines += fs.trusted_lines
        self.adapter_lines += fs.adapter_lines
        self.wrapper_lines += fs.wrapper_lines
        self.files.append(fs)

def is_boilerplate(stripped):
    """Boilerplate: structural lines excluded from all categories."""
    if not stripped:
        return True
    if stripped.startswith('//'):
        return True
    if stripped.startswith('use ') or stripped.startswith('pub use '):
        return True
    if stripped.startswith('#[') or stripped.startswith('#!['):
        return True
    if stripped.startswith('pub mod') or stripped.startswith('mod '):
        return True
    if stripped in ('verus! {', '} // end verus!', '{', '}'):
        return True
    if stripped.startswith('#[cfg('):
        return True
    return False

_VIS = r'(?:pub(?:\([^)]*\))?\s+)?'
_WRAPPER_PATTERNS = None

def _get_wrapper_patterns():
    global _WRAPPER_PATTERNS
    if _WRAPPER_PATTERNS is None:
        _WRAPPER_PATTERNS = [
            re.compile(_VIS + r'(?:struct|enum|union|trait)\s+'),
            re.compile(r'(?:unsafe\s+)?impl\b'),
            re.compile(_VIS + r'(?:unsafe\s+)?(?:async\s+)?(?:fn|exec\s+fn)\s+'),
            re.compile(_VIS + r'(?:static|const)\s+(?!fn\b)\w+\s*:'),
            re.compile(_VIS + r'type\s+\w+'),
        ]
    return _WRAPPER_PATTERNS

def is_wrapper_boilerplate(stripped):
    """Extra structural lines excluded only outside verus! blocks
    (trusted/wrapper code): fn signatures, struct/enum defs, impl headers, etc.
    """
    if stripped.startswith('thread_local!'):
        return True
    for pat in _get_wrapper_patterns():
        if pat.match(stripped):
            return True
    return False

def classify_file(path, spec_only=False):
    """Classify each line of a .rs file."""
    fs = FileStats(path)
    with open(path, 'r') as f:
        lines = f.readlines()

    is_trusted_module = any('verus::trusted' in line for line in lines[:10])

    in_verus_block = False
    verus_depth = 0

    ctx = 'exec'
    depth = 0
    fn_stack = []
    pending_fn = None
    in_contract = False

    for i, line in enumerate(lines):
        stripped = line.strip()
        opens = stripped.count('{')
        closes = stripped.count('}')
        net_opens = opens - closes

        if stripped == 'verus! {':
            in_verus_block = True
            verus_depth = depth + opens

        if in_verus_block and stripped == '} // end verus!':
            in_verus_block = False
        elif in_verus_block and depth + net_opens < verus_depth:
            in_verus_block = False

        if not in_verus_block:
            if not is_boilerplate(stripped) and not is_wrapper_boilerplate(stripped):
                if is_trusted_module:
                    fs.adapter_lines += 1
                else:
                    fs.wrapper_lines += 1
            depth += net_opens
            continue

        if stripped.startswith(('requires', 'ensures', 'decreases', 'recommends')) or \
           re.match(r'invariant\b', stripped):
            in_contract = True

        is_spec = bool(re.match(r'.*\b(open\s+|closed\s+)?spec\s+fn\b', stripped))
        is_proof = bool(re.match(r'.*\bproof\s+fn\b', stripped))
        is_ext_body = False

        if re.match(r'.*\b(pub\s+)?(fn|exec\s+fn)\b', stripped) and not is_spec and not is_proof:
            for j in range(max(0, i-3), i):
                if 'external_body' in lines[j] or re.search(r'verifier::external\b(?!_)', lines[j]):
                    is_ext_body = True
                    break

        fn_entered = False

        if is_spec or is_proof:
            if net_opens > 0:
                fn_stack.append((ctx, depth + opens))
                ctx = 'spec'
                fn_entered = True
            else:
                pending_fn = ('spec', depth)
        elif is_ext_body:
            if net_opens > 0:
                fn_stack.append((ctx, depth + opens))
                ctx = 'trusted'
                fn_entered = True
            else:
                pending_fn = ('trusted', depth)

        if re.match(r'\s*proof\s*\{', stripped) and ctx == 'exec' and not is_proof:
            fn_stack.append((ctx, depth + opens))
            ctx = 'spec'
            pending_fn = None
            fn_entered = True

        if pending_fn and net_opens > 0 and not (is_spec or is_proof or is_ext_body):
            fn_stack.append((ctx, depth + opens))
            ctx = pending_fn[0]
            pending_fn = None
            fn_entered = True

        if pending_fn and (is_spec or is_proof or is_ext_body) and net_opens > 0:
            pending_fn = None

        new_depth = depth + net_opens
        is_fn_open = stripped == '{' and fn_entered
        is_fn_close = stripped == '}' and fn_stack and new_depth < fn_stack[-1][1]

        if is_boilerplate(stripped):
            if stripped in ('{', '}') and ctx == 'trusted' and not is_fn_open and not is_fn_close:
                fs.trusted_lines += 1
            elif stripped in ('{', '}') and ctx == 'exec' and not is_fn_open:
                fs.exec_lines += 1
            elif pending_fn or ctx == 'spec':
                fs.spec_proof_lines += 1
            else:
                pass
        elif in_contract or pending_fn:
            fs.spec_proof_lines += 1
        elif ctx == 'spec':
            fs.spec_proof_lines += 1
        elif ctx == 'trusted':
            fs.trusted_lines += 1
        elif re.match(r'\s*assert\b', stripped):
            fs.spec_proof_lines += 1
        else:
            if spec_only:
                fs.spec_proof_lines += 1
            else:
                fs.exec_lines += 1

        depth = new_depth

        while fn_stack and depth < fn_stack[-1][1]:
            ctx, _ = fn_stack.pop()

        if net_opens > 0:
            in_contract = False

    if spec_only:
        fs.spec_proof_lines += fs.exec_lines + fs.trusted_lines + fs.adapter_lines + fs.wrapper_lines
        fs.exec_lines = 0
        fs.trusted_lines = 0
        fs.adapter_lines = 0
        fs.wrapper_lines = 0

    return fs

def scan_directory(directory, spec_only=False):
    stats = Stats()
    abs_dir = os.path.abspath(directory)
    tests_dir = os.path.join(abs_dir, 'tests')
    for root, dirs, files in os.walk(directory):
        if os.path.abspath(root).startswith(tests_dir):
            continue
        for f in sorted(files):
            if f.endswith('.rs'):
                path = os.path.join(root, f)
                fs = classify_file(path, spec_only=spec_only)
                stats.add(fs)
    return stats

def main():
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <directory> [--verbose] [--spec-only]")
        sys.exit(1)

    directory = sys.argv[1]
    verbose = '--verbose' in sys.argv
    spec_only = '--spec-only' in sys.argv

    stats = scan_directory(directory, spec_only=spec_only)

    print(f"{'─'*60}")
    print(f"  {directory}")
    print(f"{'─'*60}")

    total = stats.exec_lines + stats.spec_proof_lines + stats.trusted_lines + stats.adapter_lines + stats.wrapper_lines

    if verbose:
        print(f"\n  {'File':<40} {'Exec':>6} {'Spec':>6} {'Trust':>6} {'Adapt':>6} {'Wrap':>6}")
        print(f"  {'─'*40} {'─'*6} {'─'*6} {'─'*6} {'─'*6} {'─'*6}")
        for fs in stats.files:
            name = os.path.relpath(fs.path, directory)
            print(f"  {name:<40} {fs.exec_lines:>6} {fs.spec_proof_lines:>6} {fs.trusted_lines:>6} {fs.adapter_lines:>6} {fs.wrapper_lines:>6}")
        print()

    print(f"  {'Executable code:':<40} {stats.exec_lines:>6} lines")
    print(f"  {'Spec + Proof:':<40} {stats.spec_proof_lines:>6} lines")
    print(f"  {'Trusted (TCB):':<40} {stats.trusted_lines:>6} lines")
    print(f"  {'Adapter:':<40} {stats.adapter_lines:>6} lines")
    print(f"  {'Wrapper:':<40} {stats.wrapper_lines:>6} lines")

    if total > 0:
        print(f"\n  Exec: {stats.exec_lines/total*100:.1f}%  "
              f"Spec: {stats.spec_proof_lines/total*100:.1f}%  "
              f"Trusted: {stats.trusted_lines/total*100:.1f}%  "
              f"Adapter: {stats.adapter_lines/total*100:.1f}%  "
              f"Wrapper: {stats.wrapper_lines/total*100:.1f}%")

if __name__ == '__main__':
    main()

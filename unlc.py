#!/usr/bin/env python3
r"""unlc: compile a small call-by-value lambda language (S-expressions) to Unlambda.

Usage: python3 unlc.py json2dir.lam > json2dir.unl

Source language
  (def name expr)          global definition; a self-reference makes it recursive (Z combinator)
  (primitive read-byte)    define the compiler-generated I/O primitives at this point
  (primitive print-byte)
  (main expr)              the program
Expressions
  x  (f a b ...)  (f)=(f unit)  (fn (a b) body...)  (fn () body...)
  (let ((x e) ...) body...)  (begin e ...)  (if c a b)  (cond (c e) ... (else e))
  (and a ...)  (or a ...)  (match e (() nil-branch) ((h t) cons-branch) ...)
  (match-pair e (a b) body...)  (destr (x1 x2 ... rest) e body...)
  (bl 1 0 x ...)  list of booleans (1/0 constants, symbols are variables)
  (print "text")  (fail "message")  prints "json2dir: message" and aborts the program
  42 0x2a #\c     byte constant (list of 8 booleans, most significant bit first)
  "text"          list of byte constants
  unit            the identity combinator i

Data encodings (Scott): true = \t f. t i, false = \t f. f i, nil = \n c. n i,
cons h t = \n c. c h t; a constructor with arguments is applied to the branch function,
a constructor without arguments applies its branch to i.

Bracket abstraction keeps call-by-value semantics under Unlambda's eager evaluation:
a body that is not a value is never put under k (that would evaluate it too early);
closed non-value bodies become promises `d`kE, the rest is threaded with s.
"""
import sys
import threading

# ---------------------------------------------------------------- Unlambda terms

class U:
    __slots__ = ('k', 'a', 'b', 'fv', 'size', 'val')

    def __init__(self, k, a=None, b=None):
        self.k = k
        self.a = a
        self.b = b
        if k == 'P':
            self.fv = frozenset()
            self.size = len(a)
            self.val = True
        elif k == 'V':
            self.fv = frozenset([a])
            self.size = 1
            self.val = True
        elif k == 'D':
            self.fv = a.fv
            self.size = a.size + 2
            self.val = True
        else:
            self.fv = a.fv | b.fv if b.fv else a.fv
            self.size = a.size + b.size + 1
            # partial applications of s and k are values
            if a.k == 'P' and a.a in ('s', 'k'):
                self.val = b.val
            elif a.k == 'A' and a.a.k == 'P' and a.a.a == 's':
                self.val = a.val and b.val
            else:
                self.val = False


def P(s): return U('P', s)
def V(n): return U('V', n)
def A(f, x): return U('A', f, x)
def D(x): return U('D', x)


S, K, I, DD, C = P('s'), P('k'), P('i'), P('d'), P('c')
KD = A(K, DD)


def abstract(x, t):
    if x not in t.fv:
        return A(K, t) if t.val else D(A(K, t))
    if t.k == 'V':
        return I
    if t.k == 'D':
        # promise of ([x]X applied to x): ``s`kd F
        return A(A(S, KD), abstract(x, t.a))
    f, a = t.a, t.b
    if a.k == 'V' and a.a == x and x not in f.fv:
        return f if f.val else D(f)
    return A(A(S, abstract(x, f)), abstract(x, a))


def serialize(t):
    out = []
    stack = [t]
    while stack:
        n = stack.pop()
        if n.k == 'P':
            out.append(n.a)
        elif n.k == 'A':
            out.append('`')
            stack.append(n.b)
            stack.append(n.a)
        elif n.k == 'D':
            out.append('`d')
            stack.append(n.a)
        else:
            raise SystemExit('unlc: unbound variable %s' % n.a)
    return ''.join(out)

# ---------------------------------------------------------------- reader

class Str:
    def __init__(self, b): self.b = b


class Chr:
    def __init__(self, c): self.c = c


def tokenize(src):
    i, n = 0, len(src)
    toks = []
    while i < n:
        c = src[i]
        if c in ' \t\r\n':
            i += 1
        elif c == ';':
            while i < n and src[i] != '\n':
                i += 1
        elif c in '()':
            toks.append(c)
            i += 1
        elif c == '"':
            i += 1
            buf = bytearray()
            while src[i] != '"':
                if src[i] == '\\':
                    e = src[i + 1]
                    i += 2
                    if e == 'n': buf.append(10)
                    elif e == 't': buf.append(9)
                    elif e == 'x':
                        buf.append(int(src[i:i + 2], 16))
                        i += 2
                    else: buf += e.encode()
                else:
                    buf += src[i].encode()
                    i += 1
            i += 1
            toks.append(Str(bytes(buf)))
        elif src.startswith('#\\', i):
            toks.append(Chr(ord(src[i + 2])))
            i += 3
        else:
            j = i
            while j < n and src[j] not in ' \t\r\n();"':
                j += 1
            w = src[i:j]
            i = j
            try:
                toks.append(int(w, 0))
            except ValueError:
                toks.append(w)
    return toks


def read_all(toks):
    pos = 0

    def rd():
        nonlocal pos
        t = toks[pos]
        pos += 1
        if t == '(':
            lst = []
            while toks[pos] != ')':
                lst.append(rd())
            pos += 1
            return lst
        if t == ')':
            raise SystemExit('unlc: unexpected )')
        return t

    forms = []
    while pos < len(toks):
        forms.append(rd())
    return forms

# ---------------------------------------------------------------- compiler

class Compiler:
    def __init__(self):
        self.globals = {}       # name -> ('inline', U) | ('var', U)
        self.order = []         # let-bound globals in definition order
        self.gen = 0
        self.uses = {}
        self.byte_cache = {}
        self.TRUE = self.c(['fn', ['%t', '%f'], ['%t', 'unit']], set())
        self.FALSE = self.c(['fn', ['%t', '%f'], ['%f', 'unit']], set())
        self.NIL = self.c(['fn', ['%n', '%c'], ['%n', 'unit']], set())
        self.Z = self.c(['fn', ['%f'], [['fn', ['%x'], ['%f', ['fn', ['%v'], ['%x', '%x', '%v']]]],
                                        ['fn', ['%x'], ['%f', ['fn', ['%v'], ['%x', '%x', '%v']]]]]], set())

    def sym(self):
        self.gen += 1
        return '%%g%d' % self.gen

    # constants
    def cons_const(self, h, t):
        return self.c(['fn', ['%n', '%c'], ['%c', ['%lit', h], ['%lit', t]]], set())

    def list_const(self, items):
        r = self.NIL
        for x in reversed(items):
            r = self.cons_const(x, r)
        return r

    def byte(self, v):
        if v not in self.byte_cache:
            bits = [(v >> (7 - j)) & 1 for j in range(8)]
            self.byte_cache[v] = self.list_const([self.TRUE if b else self.FALSE for b in bits])
        return self.byte_cache[v]

    def print_chain(self, bs):
        if not bs:
            return I
        t = P('.' + chr(bs[0]))
        for b in bs[1:]:
            t = A(t, P('.' + chr(b)))
        return A(t, I)

    # expressions
    def c(self, e, scope):
        if isinstance(e, str):
            if e in scope:
                return V(e)
            if e == 'unit':
                return I
            if e == 'abort':
                return V('abort')
            if e in self.globals:
                kind, u = self.globals[e]
                return u if kind == 'inline' else V('%G:' + e)
            if e == self.current:
                return V('%G:' + e)
            raise SystemExit('unlc: unknown name %s' % e)
        if isinstance(e, int):
            return self.byte(e)
        if isinstance(e, Chr):
            return self.byte(e.c)
        if isinstance(e, Str):
            return self.list_const([self.byte(b) for b in e.b])
        if isinstance(e, U):
            return e
        head = e[0]
        if head == '%lit':
            return e[1]
        if isinstance(head, str) and not (head in scope):
            m = getattr(self, 'f_' + head.replace('-', '_'), None)
            if m is not None:
                return m(e, scope)
        if len(e) == 1:
            return A(self.c(head, scope), I)
        t = self.c(head, scope)
        for a in e[1:]:
            t = A(t, self.c(a, scope))
        return t

    def body(self, es):
        return es[0] if len(es) == 1 else ['begin'] + es

    def f_fn(self, e, scope):
        params = e[1] or [self.sym()]
        inner = scope | set(params)
        t = self.c(self.body(e[2:]), inner)
        for p in reversed(params):
            t = abstract(p, t)
        return t

    def f_let(self, e, scope):
        binds, rest = e[1], e[2:]
        if not binds:
            return self.c(self.body(rest), scope)
        (x, v) = binds[0]
        return self.c([['fn', [x], ['let', binds[1:]] + rest], v], scope)

    def f_begin(self, e, scope):
        es = e[1:]
        if len(es) == 1:
            return self.c(es[0], scope)
        return self.c([['fn', [self.sym()], ['begin'] + es[1:]], es[0]], scope)

    def f_if(self, e, scope):
        return self.c([e[1], ['fn', [], e[2]], ['fn', [], e[3]]], scope)

    def f_cond(self, e, scope):
        clauses = e[1:]
        c0, v0 = clauses[0]
        if c0 == 'else':
            return self.c(v0, scope)
        return self.c(['if', c0, v0, ['cond'] + clauses[1:]], scope)

    def f_and(self, e, scope):
        if len(e) == 2:
            return self.c(e[1], scope)
        return self.c(['if', e[1], ['and'] + e[2:], 'false'], scope)

    def f_or(self, e, scope):
        if len(e) == 2:
            return self.c(e[1], scope)
        return self.c(['if', e[1], 'true', ['or'] + e[2:]], scope)

    def f_match(self, e, scope):
        return self.c([e[1]] + [['fn'] + br for br in e[2:]], scope)

    def f_match_pair(self, e, scope):
        return self.c([e[1], ['fn', e[2]] + e[3:]], scope)

    def f_destr(self, e, scope):
        names, val, rest = e[1], e[2], e[3:]
        if len(names) == 1:
            return self.c(['let', [[names[0], val]]] + rest, scope)
        r = self.sym()
        return self.c(['match', val, [[], 'unit'],
                       [[names[0], r], ['destr', names[1:], r] + rest]], scope)

    def f_bl(self, e, scope):
        t = 'nil'
        for x in reversed(e[1:]):
            x = {1: 'true', 0: 'false'}.get(x, x) if isinstance(x, int) else x
            t = ['cons', x, t]
        return self.c(t, scope)

    def f_print(self, e, scope):
        return self.print_chain(e[1].b)

    def f_fail(self, e, scope):
        msg = Str(b'json2dir: ' + e[1].b + b'\n')
        return self.c(['begin', ['print', msg], ['abort', 'unit']], scope)

    # generated primitives
    def prim_read_byte(self):
        # @ reads a byte (i on success, v at EOF); ?x tests it. An i/v answer is turned
        # into control flow with call/cc: `(b thunk) i` runs the thunk for i and is v for v.
        order = []
        for ch in '" e:a,tnoirsldcumhfpgwybvk{}\n.\\-_0123456789xjqz[]\t\r/':
            if ord(ch) not in order:
                order.append(ord(ch))
        order += [b for b in range(32, 127) if b not in order]
        order += [b for b in range(0, 32) if b not in order]
        order += [b for b in range(127, 256)]
        assert len(order) == 256
        tests = []
        for b in order[:-1]:
            tests.append([['%lit', P('?' + chr(b))],
                          ['fn', ['%b'], ['%b', ['fn', [], ['%ret', ['some', b]]], 'unit']]])
        decode = ['begin'] + tests + [['%ret', ['some', order[-1]]]]
        return ['fn', ['%u'],
                [['%lit', C], ['fn', ['%ret'],
                               ['begin',
                                [['%lit', P('@')], ['fn', ['%b'], ['%b', ['fn', [], decode], 'unit']]],
                                ['%ret', 'none']]]]]

    def prim_print_byte(self):
        def tree(prefix, v):
            if len(prefix) == 8:
                b = int(''.join(map(str, prefix)), 2)
                return [['%lit', P('.' + chr(b))], 'unit']
            h, t = self.sym(), self.sym()
            return ['match', v, [[], 'unit'],
                    [[h, t], ['if', h, tree(prefix + [1], t), tree(prefix + [0], t)]]]
        return ['fn', ['%bs'], tree([], '%bs')]

    # program
    def count_uses(self, forms):
        def walk(e):
            if isinstance(e, str):
                self.uses[e] = self.uses.get(e, 0) + 1
            elif isinstance(e, list):
                for x in e:
                    walk(x)
        for f in forms:
            walk(f[2:] if f[0] == 'def' else f[1:])

    def define(self, name, expr, inline_max):
        self.current = name
        u = self.c(expr, set())
        self.current = None
        if '%G:' + name in u.fv:
            u = A(self.Z, abstract('%G:' + name, u))
        if self.uses.get(name, 0) <= 1 or u.size <= inline_max:
            self.globals[name] = ('inline', u)
        else:
            self.globals[name] = ('var', u)
            self.order.append(name)

    def program(self, forms, inline_max):
        self.count_uses(forms)
        self.current = None
        main = None
        for f in forms:
            if f[0] == 'def':
                self.define(f[1], f[2], inline_max)
            elif f[0] == 'primitive':
                self.define(f[1], getattr(self, 'prim_' + f[1].replace('-', '_'))(), inline_max)
            elif f[0] == 'main':
                main = self.c(f[1], set())
            else:
                raise SystemExit('unlc: unknown top-level form %r' % (f[0],))
        body = main
        for name in reversed(self.order):
            body = A(abstract('%G:' + name, body), self.globals[name][1])
        top = A(C, abstract('abort', body))
        if top.fv:
            raise SystemExit('unlc: unbound names %s' % sorted(top.fv))
        return top


def main():
    args = sys.argv[1:]
    inline_max = 200
    if args and args[0].startswith('--inline='):
        inline_max = int(args[0].split('=')[1])
        args = args[1:]
    with open(args[0], encoding='utf-8') as fh:
        forms = read_all(tokenize(fh.read()))
    comp = Compiler()
    top = comp.program(forms, inline_max)
    code = serialize(top)
    sys.stderr.write('unlc: %d bytes, %d let-bound globals\n' % (len(code), len(comp.order)))
    # no trailing newline: the interpreter reads the program from stdin and the
    # document starts right after the last character of the program
    sys.stdout.buffer.write(code.encode('latin-1'))


if __name__ == '__main__':
    sys.setrecursionlimit(1000000)
    threading.stack_size(512 * 1024 * 1024)
    status = []

    def run():
        try:
            main()
        except BaseException as ex:
            status.append(ex)
    th = threading.Thread(target=run)
    th.start()
    th.join()
    if status:
        raise status[0]

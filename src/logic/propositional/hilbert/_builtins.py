from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from typing import Any

from prelude.formula import Builtins as FoundationBuiltins
from prelude.formula import GLOBAL_PRELUDE_MODULE_ID
from skfd.authoring.formula import TokenSeq, Wff
from skfd.core.peg import Rule, TokenStream
from skfd.core.symbols import SymbolId, SymbolInterner


@dataclass(frozen=True)
class PropositionalBuiltins:
    """Logic-owned propositional vocabulary layered over the foundation prelude."""

    lp: SymbolId
    rp: SymbolId
    imp: SymbolId
    neg: SymbolId
    and_: SymbolId
    iff: SymbolId
    or_: SymbolId
    tru: SymbolId
    fal: SymbolId

    @staticmethod
    def ensure(
        interner: SymbolInterner,
        *,
        origin_module_id: str = GLOBAL_PRELUDE_MODULE_ID,
        origin_ref: Any = None,
    ) -> PropositionalBuiltins:
        foundation = FoundationBuiltins.ensure(
            interner,
            origin_module_id=origin_module_id,
            origin_ref=origin_ref,
        )
        and_ = interner.intern(
            origin_module_id=origin_module_id, local_name="/\\", kind="Const", origin_ref=origin_ref
        )
        iff = interner.intern(
            origin_module_id=origin_module_id, local_name="<->", kind="Const", origin_ref=origin_ref
        )
        or_ = interner.intern(
            origin_module_id=origin_module_id, local_name="\\/", kind="Const", origin_ref=origin_ref
        )
        tru = interner.intern(
            origin_module_id=origin_module_id, local_name="T.", kind="Const", origin_ref=origin_ref
        )
        fal = interner.intern(
            origin_module_id=origin_module_id, local_name="F.", kind="Const", origin_ref=origin_ref
        )
        return PropositionalBuiltins(
            lp=foundation.lp,
            rp=foundation.rp,
            imp=foundation.imp,
            neg=foundation.neg,
            and_=and_,
            iff=iff,
            or_=or_,
            tru=tru,
            fal=fal,
        )


def imp(b: PropositionalBuiltins, phi: Wff, psi: Wff) -> Wff:
    return Wff("wff", (b.lp, *phi.tokens, b.imp, *psi.tokens, b.rp))


def wn(b: PropositionalBuiltins, phi: Wff) -> Wff:
    return Wff("wff", (b.neg, *phi.tokens))


def wa(b: PropositionalBuiltins, phi: Wff, psi: Wff) -> Wff:
    return Wff("wff", (b.lp, *phi.tokens, b.and_, *psi.tokens, b.rp))


def wo(b: PropositionalBuiltins, phi: Wff, psi: Wff) -> Wff:
    return Wff("wff", (b.lp, *phi.tokens, b.or_, *psi.tokens, b.rp))


def wb(b: PropositionalBuiltins, phi: Wff, psi: Wff) -> Wff:
    return Wff("wff", (b.lp, *phi.tokens, b.iff, *psi.tokens, b.rp))


def wtru(b: PropositionalBuiltins) -> Wff:
    return Wff("wff", (b.tru,))


def wfal(b: PropositionalBuiltins) -> Wff:
    return Wff("wff", (b.fal,))


@dataclass(frozen=True)
class ImpShape:
    phi: TokenSeq
    psi: TokenSeq


@dataclass(frozen=True)
class NegShape:
    body: TokenSeq


@dataclass(frozen=True)
class AndShape:
    left: TokenSeq
    right: TokenSeq


@dataclass(frozen=True)
class _Tok:
    type: str
    value: SymbolId
    pos: int


def _peg_tokenize(b: PropositionalBuiltins, tokens: Sequence[SymbolId]) -> list[_Tok]:
    out: list[_Tok] = []
    for i, t in enumerate(tokens):
        if t == b.lp:
            out.append(_Tok("LPAREN", t, i))
        elif t == b.rp:
            out.append(_Tok("RPAREN", t, i))
        else:
            out.append(_Tok("SYM", t, i))
    out.append(_Tok("EOF", -1, len(tokens)))
    return out


def _peg_bal(
    b: PropositionalBuiltins,
) -> tuple[Rule[TokenSeq], Rule[TokenSeq]]:
    def sym_fn(s: TokenStream, i: int) -> tuple[TokenSeq, int] | None:
        tok = s.peek(i)
        if tok.type != "SYM":
            return None
        return (tok.value,), i + 1

    sym = Rule("bal.sym", sym_fn)

    def group_fn(s: TokenStream, i: int) -> tuple[TokenSeq, int] | None:
        tok = s.peek(i)
        if tok.type != "LPAREN":
            return None
        inner_out = bal(s, i + 1)
        if inner_out is None:
            return None
        inner, j = inner_out
        close = s.peek(j)
        if close.type != "RPAREN":
            return None
        return (b.lp, *inner, b.rp), j + 1

    group = Rule("bal.group", group_fn)

    def bal_fn(s: TokenStream, i: int) -> tuple[TokenSeq, int] | None:
        acc: list[SymbolId] = []
        j = i
        while True:
            tok = s.peek(j)
            if tok.type in ("RPAREN", "EOF"):
                break
            part: tuple[TokenSeq, int] | None
            if tok.type == "LPAREN":
                part = group(s, j)
            else:
                part = sym(s, j)
            if part is None:
                return None
            frag, j = part
            acc.extend(frag)
        return tuple(acc), j

    bal = Rule("bal", bal_fn)
    return bal, group


def _peg_try_parse_split_binary(
    b: PropositionalBuiltins, tokens: Sequence[SymbolId], *, op: SymbolId
) -> tuple[TokenSeq, TokenSeq] | None:
    ts: TokenStream[TokenSeq] = TokenStream(text="", tokens=_peg_tokenize(b, tokens))
    bal, group = _peg_bal(b)

    def sym_any_fn(s: TokenStream, i: int) -> tuple[TokenSeq, int] | None:
        tok = s.peek(i)
        if tok.type != "SYM":
            return None
        return (tok.value,), i + 1

    sym_any = Rule("bal_no_op.sym", sym_any_fn)

    def bal_no_op_fn(s: TokenStream, i: int) -> tuple[TokenSeq, int] | None:
        acc: list[SymbolId] = []
        j = i
        while True:
            tok = s.peek(j)
            if tok.type in ("RPAREN", "EOF"):
                break
            if tok.type == "SYM" and tok.value == op:
                break
            part: tuple[TokenSeq, int] | None
            if tok.type == "LPAREN":
                part = group(s, j)
            else:
                part = sym_any(s, j)
            if part is None:
                return None
            frag, j = part
            acc.extend(frag)
        return tuple(acc), j

    bal_no_op = Rule("bal_no_op", bal_no_op_fn)

    i = 0
    if ts.peek(i).type != "LPAREN":
        return None
    left_out = bal_no_op(ts, i + 1)
    if left_out is None:
        return None
    left, j = left_out
    if not left:
        return None
    mid = ts.peek(j)
    if mid.type != "SYM" or mid.value != op:
        return None
    right_out = bal(ts, j + 1)
    if right_out is None:
        return None
    right, k = right_out
    if not right:
        return None
    if ts.peek(k).type != "RPAREN":
        return None
    if ts.peek(k + 1).type != "EOF":
        return None
    return left, right


def try_parse_imp(b: PropositionalBuiltins, tokens: Sequence[SymbolId]) -> ImpShape | None:
    parts = _peg_try_parse_split_binary(b, tokens, op=b.imp)
    if parts is None:
        return None
    left, right = parts
    return ImpShape(phi=left, psi=right)


def try_parse_wn(b: PropositionalBuiltins, tokens: Sequence[SymbolId]) -> NegShape | None:
    toks = tuple(tokens)
    if len(toks) < 2 or toks[0] != b.neg:
        return None
    ts: TokenStream[TokenSeq] = TokenStream(text="", tokens=_peg_tokenize(b, toks[1:]))
    bal, _ = _peg_bal(b)
    out = bal(ts, 0)
    if out is None:
        return None
    body, j = out
    if not body or ts.peek(j).type != "EOF":
        return None
    return NegShape(body=body)


def try_parse_wa(b: PropositionalBuiltins, tokens: Sequence[SymbolId]) -> AndShape | None:
    parts = _peg_try_parse_split_binary(b, tokens, op=b.and_)
    if parts is None:
        return None
    left, right = parts
    return AndShape(left=left, right=right)


__all__ = [
    "PropositionalBuiltins",
    "ImpShape",
    "NegShape",
    "AndShape",
    "imp",
    "wn",
    "wa",
    "wo",
    "wb",
    "wtru",
    "wfal",
    "try_parse_imp",
    "try_parse_wn",
    "try_parse_wa",
]

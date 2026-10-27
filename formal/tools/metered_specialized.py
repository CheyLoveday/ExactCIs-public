"""Native selected-embedding root-data generation with degree-lowering restarts.

Reducible definers are localized by gcd, never by irreducible factorization.
A nonunit at irrelevant roots removes that factor; a zero at the selected
embedding retains its gcd factor. Every change restarts packet construction
and strictly lowers the rational definer degree. All work uses one meter.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q

import metered_algebraic as a
import metered_parametric as f
import metered_polynomial as p
import metered_root as r


class Restart(RuntimeError):
    def __init__(self, root: a.Root):
        self.root = root
        super().__init__("selected definer strictly localized; restart packet")


@dataclass(frozen=True)
class Context:
    root: a.Root

    def _localize(self, common: p.P, m: r.Meter) -> None:
        certificate = r.generate_witness_with_meter(common, m)
        count = r.count_with_meter(
            common, certificate, m, self.root.lower, self.root.upper
        )
        if count == 1:
            retained = common
        elif count == 0:
            retained = p.exact_divide(self.root.definer, common, m)
        else:
            raise r.InvalidWitness(
                "gcd localization contradicted a singleton embedding"
            )
        if len(retained) >= len(self.root.definer):
            raise r.InvalidWitness("localization did not strictly lower definer degree")
        next_certificate = r.generate_witness_with_meter(retained, m)
        result = a.Root(retained, self.root.lower, self.root.upper, next_certificate)
        a.check_root(result, m)
        raise Restart(result)

    def _residue(self, value: p.P, m: r.Meter) -> p.P:
        _, residue = p.divide(value, self.root.definer, m)
        if not residue:
            return ()
        common, _, _ = p.xgcd(self.root.definer, residue, m)
        if len(common) > 1:
            self._localize(common, m)
        return residue

    def normalize(
        self, numerator: p.P, denominator: p.P, m: r.Meter
    ) -> tuple[p.P, p.P]:
        numerator = self._residue(numerator, m)
        denominator = self._residue(denominator, m)
        if not denominator:
            raise r.InvalidWitness("selected field division used an actual zero")
        common, inverse, _ = p.xgcd(denominator, self.root.definer, m)
        if not p.equal(common, p.ONE, m):
            raise r.InvalidWitness("selected denominator did not become a unit")
        return self._residue(p.mul(numerator, inverse, m), m), p.ONE


@dataclass(frozen=True)
class Certificate:
    representative: f.B
    quotient: f.B
    power_quotient: f.B
    exponent: int
    root_witness: f.B
    power_witness: f.B
    bezout_left: f.B
    bezout_right: f.B
    bezout_witness: f.B
    tail: tuple[f.B, ...]
    quotients: tuple[f.B, ...]
    witnesses: tuple[f.B, ...]
    last: p.P
    last_inverse: p.P
    last_quotient: p.P
    derivative_witness: f.B


def _identity(left: f.B, right: f.B, definer: p.P, m: r.Meter) -> f.B:
    difference = f._badd(left, f._bscale((Q(-1),), right, m), m)
    m.structural(len(difference))
    return tuple(p.exact_divide(coefficient, definer, m) for coefficient in difference)


def _verify_identity(
    left: f.B, right: f.B, witness: f.B, definer: p.P, m: r.Meter
) -> None:
    difference = f._badd(left, f._bscale((Q(-1),), right, m), m)
    if len(difference) != len(witness):
        raise r.InvalidWitness(
            "modular identity witness had the wrong coefficient count"
        )
    for coefficient, quotient in zip(difference, witness):
        m.structural()
        if not p.equal(coefficient, p.mul(definer, quotient, m), m):
            raise r.InvalidWitness("generated modular identity failed replay")


def replay(original: f.B, root: a.Root, c: Certificate, m: r.Meter) -> None:
    a.check_root(root, m)
    if c.exponent <= 0:
        raise r.InvalidWitness("selected root exponent must be positive")
    _verify_identity(
        original,
        f._bmul(c.representative, c.quotient, m),
        c.root_witness,
        root.definer,
        m,
    )
    _verify_identity(
        f._bpower(c.representative, c.exponent, m),
        f._bmul(original, c.power_quotient, m),
        c.power_witness,
        root.definer,
        m,
    )
    _verify_identity(
        f._badd(
            f._bmul(c.bezout_left, c.representative, m),
            f._bmul(c.bezout_right, f._bderivative(c.representative, m), m),
            m,
        ),
        (p.ONE,),
        c.bezout_witness,
        root.definer,
        m,
    )
    chain = (c.representative, *c.tail)
    if (
        len(c.quotients) != max(0, len(chain) - 2)
        or len(c.witnesses) != len(c.quotients) + 1
    ):
        raise r.InvalidWitness("selected signed chain shape failed")
    for i, quotient in enumerate(c.quotients):
        _verify_identity(
            chain[i],
            f._badd(
                f._bmul(chain[i + 1], quotient, m),
                f._bscale((Q(-1),), chain[i + 2], m),
                m,
            ),
            c.witnesses[i],
            root.definer,
            m,
        )
    _verify_identity(chain[-1], (c.last,), c.witnesses[-1], root.definer, m)
    if not p.equal(
        p.mul(c.last, c.last_inverse, m),
        p.add(p.ONE, p.mul(root.definer, c.last_quotient, m), m),
        m,
    ):
        raise r.InvalidWitness("selected terminal inverse identity failed")
    if c.tail:
        _verify_identity(
            c.tail[0],
            f._bderivative(c.representative, m),
            c.derivative_witness,
            root.definer,
            m,
        )


def generate(original: f.B, selected: a.Root, m: r.Meter) -> tuple[a.Root, Certificate]:
    current = selected
    a.check_root(current, m)
    while True:
        m.structural()
        context = Context(current)
        try:
            h = f._trim(
                tuple(f._element(row, p.ONE, m, context) for row in original), m
            )
            data = f._root_data(h, m)

            def encode(poly: f.F) -> f.B:
                m.structural(len(poly))
                if any(
                    not p.equal(coefficient.denominator, p.ONE, m)
                    for coefficient in poly
                ):
                    raise r.InvalidWitness(
                        "selected coefficient retained an unrealized denominator"
                    )
                return tuple(coefficient.numerator for coefficient in poly)

            representative, quotient, power_quotient = (
                encode(data.representative),
                encode(data.quotient),
                encode(data.power_quotient),
            )
            bezout_left, bezout_right = encode(data.bezout_left), encode(
                data.bezout_right
            )
            chain = tuple(encode(poly) for poly in data.chain)
            quotients = tuple(encode(poly) for poly in data.quotients)
            last = chain[-1][0]
            inverse = f._inverse(f._element(last, p.ONE, m, context), m).numerator
            last_quotient = p.exact_divide(
                p.add(p.mul(last, inverse, m), (Q(-1),), m), current.definer, m
            )
            witnesses = tuple(
                _identity(
                    chain[i],
                    f._badd(
                        f._bmul(chain[i + 1], q, m),
                        f._bscale((Q(-1),), chain[i + 2], m),
                        m,
                    ),
                    current.definer,
                    m,
                )
                for i, q in enumerate(quotients)
            )
            terminal_witness = _identity(chain[-1], (last,), current.definer, m)
            c = Certificate(
                representative,
                quotient,
                power_quotient,
                data.exponent,
                _identity(
                    original, f._bmul(representative, quotient, m), current.definer, m
                ),
                _identity(
                    f._bpower(representative, data.exponent, m),
                    f._bmul(original, power_quotient, m),
                    current.definer,
                    m,
                ),
                bezout_left,
                bezout_right,
                _identity(
                    f._badd(
                        f._bmul(bezout_left, representative, m),
                        f._bmul(bezout_right, f._bderivative(representative, m), m),
                        m,
                    ),
                    (p.ONE,),
                    current.definer,
                    m,
                ),
                chain[1:],
                quotients,
                (*witnesses, terminal_witness),
                last,
                inverse,
                last_quotient,
                (
                    ()
                    if len(chain) == 1
                    else _identity(
                        chain[1], f._bderivative(representative, m), current.definer, m
                    )
                ),
            )
            replay(original, current, c, m)
            return current, c
        except Restart as restart:
            if len(restart.root.definer) >= len(current.definer):
                raise r.InvalidWitness(
                    "selected packet restart did not decrease degree"
                ) from restart
            current = restart.root

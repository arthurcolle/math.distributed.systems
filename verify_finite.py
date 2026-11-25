#!/usr/bin/env python3
"""Exact finite checks for two locally derived no-go examples."""

from fractions import Fraction as Q


def expectation(law, observable):
    return sum((probability * observable(state) for state, probability in law), Q(0))


def characteristic_coefficients_2x2(matrix):
    a, b = matrix[0]
    c, d = matrix[1]
    return a + d, a * d - b * c


def check_martingale_transport():
    law_a = [((Q(1), Q(1)), Q(1, 2)), ((Q(-1), Q(-1)), Q(1, 2))]
    law_b = [((Q(1), Q(-1)), Q(1, 2)), ((Q(-1), Q(1)), Q(1, 2))]
    for law in (law_a, law_b):
        assert sum((p for _, p in law), Q(0)) == 1
        for coordinate in (0, 1):
            assert expectation(law, lambda x: x[coordinate]) == 0
            assert sorted((x[coordinate], p) for x, p in law) == [
                (Q(-1), Q(1, 2)), (Q(1), Q(1, 2))]

    def covariance(law):
        return tuple(tuple(expectation(law, lambda x: x[i] * x[j])
                           for j in (0, 1)) for i in (0, 1))

    cov_a, cov_b = covariance(law_a), covariance(law_b)
    assert cov_a == ((Q(1), Q(1)), (Q(1), Q(1)))
    assert cov_b == ((Q(1), Q(-1)), (Q(-1), Q(1)))
    assert characteristic_coefficients_2x2(cov_a) == (Q(2), Q(0))
    assert characteristic_coefficients_2x2(cov_a) == characteristic_coefficients_2x2(cov_b)
    payoff = lambda x: max(x[0] + x[1] - 1, 0)
    assert expectation(law_a, payoff) == Q(1, 2)
    assert expectation(law_b, payoff) == Q(0)
    print("PASS: identical marginals and covariance spectrum; basket prices 1/2 vs 0")


def check_directed_orientation():
    cyclic = {(1, 2), (2, 3), (3, 1)}
    transitive = {(1, 2), (1, 3), (2, 3)}
    underlying = lambda edges: {frozenset(edge) for edge in edges}
    sinks = lambda edges: {vertex for vertex in (1, 2, 3)
                           if not any(source == vertex for source, _ in edges)}
    assert underlying(cyclic) == underlying(transitive)
    assert sinks(cyclic) == set()
    assert sinks(transitive) == {3}
    assert {(1, 2), (2, 3), (3, 1)} <= cyclic
    print("PASS: identical undirected triangle; cyclic vs transitive orientation")


if __name__ == "__main__":
    check_martingale_transport()
    check_directed_orientation()

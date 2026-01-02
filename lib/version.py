from collections.abc import Callable
from contextlib import suppress
from operator import eq, ge, gt, le, lt
from typing import Self

from semver import Version

OPERATOR_STR_TO_FN: dict[str, Callable] = {">": gt, ">=": ge, "<": lt, "<=": le, "": eq}


class VersionInterval:
    """Represents a single version interval, which is an operator and a version.

    Note that versions with ^, ~, or X-ranges (xX*) cannot be represented by a single
    VersionInterval. They require multiple VersionInterval objects.
    However, this class will strip the string of these characters for convenience.
    """

    def __init__(self, operator: str, version: Version, s: str = "") -> None:
        self.operator = OPERATOR_STR_TO_FN[operator]
        self.version = version
        self._s = s

    def __str__(self) -> str:
        if self._s:
            return self._s

        return f"{self.operator.__name__}{self.version}"

    def __repr__(self) -> str:
        return (
            f"VersionInterval({self.operator.__name__}, {self.version!r}, {self._s!r})"
        )

    def __eq__(self, other: object, /) -> bool:
        return (
            isinstance(other, VersionInterval)
            and self.operator == other.operator
            and self.version == other.version
        )

    def __hash__(self) -> int:
        return hash((self.operator, self.version))

    @classmethod
    def from_str(cls, s: str) -> list[Self]:
        """
        Given the version range string, produce a list of VersionIntervals
        that represent it.
        """
        # Match all versions.
        if s == "*":
            return [cls(">=", Version(0, 0, 0), s)]

        # The default case, which covers <, >, ^, ~
        operator = s[0]
        version = s[1:]

        # Check if it's <= or >=
        if operator in {"<", ">"} and s[1] == "=":
            operator = s[:2]
            version = s[2:]

        # Check if it starts with the number
        elif s[0] in [str(s) for s in range(10)]:
            operator = ""
            version = s

        # Handle ^ and ~, which create two VersionIntervals.
        # I *think* that this cannot be combined with X-ranges.
        if operator == "^":
            low = Version.parse(version, optional_minor_and_patch=True)
            high = low.bump_major()
            return [cls(">=", low), cls("<", high)]
        elif operator == "~":
            low = Version.parse(version, optional_minor_and_patch=True)
            high = low.bump_minor()
            return [cls(">=", low), cls("<", high)]

        # Handle X-ranges in the minor or patch.
        # TODO "Additional trailing .x/.X/.* are allowed but have no effect"
        X_VALS = ["x", "X", "*"]

        if any(version.endswith(c) for c in X_VALS):
            version_no_x = version.replace(".x", "").replace(".X", "").replace(".*", "")
            low = Version.parse(version_no_x, optional_minor_and_patch=True)
            for x in X_VALS:
                with suppress(ValueError):
                    x_idx = version.split(".").index(x)
                    break
            else:
                print("Something weird happened 1")
                exit(1)

            if x_idx == 1:
                high = low.bump_major()
            elif x_idx == 2:
                high = low.bump_minor()
            else:
                print("Something weird happened 2")
                exit(1)
            return [cls(">=", low), cls("<", high)]

        return [cls(operator, Version.parse(version, optional_minor_and_patch=True), s)]

    def __contains__(self, version: Version) -> bool:
        """Whether the interval contains a version."""
        return self.operator(version, self.version)

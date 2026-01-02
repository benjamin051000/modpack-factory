from operator import ge, gt, le, lt
from typing import Self

from semver import Version

MAX_VERSION_NUM = 999_999


# NOTE: This cannot be a dataclass unless you're willing to change the variable order.
class VersionInterval:
    def __init__(
        self,
        min_inclusive: bool,
        min: Version | None,
        max: Version | None,
        max_inclusive: bool,
    ) -> None:
        self.min_inclusive = min_inclusive
        self.min = min if min is not None else Version(0)
        self.max = (
            max
            if max is not None
            else Version(MAX_VERSION_NUM, MAX_VERSION_NUM, MAX_VERSION_NUM)
        )
        self.max_inclusive = max_inclusive

    def __str__(self) -> str:
        front = "[" if self.min_inclusive else "("
        back = "]" if self.max_inclusive else ")"
        return f"{front}{self.min}, {self.max}{back}"

    def __repr__(self) -> str:
        return str(self)

    @classmethod
    def from_str(cls, s: str | list[str]) -> Self:
        # Some of them come in as lists.
        if isinstance(s, list):
            if len(s) == 1:
                # Unwrap list
                s = s[0]
            # elif len(s) == 2:
            #     return cls(
            #         True,
            #         Version.parse(s[0], optional_minor_and_patch=True),
            #         Version.parse(s[1], optional_minor_and_patch=True),
            #         True,
            #     )
            else:
                raise ValueError(f"Invalid version constraint: {s}")

        # Remove things like 1.2.* or 1.2.x, we just represent those as 1.2. I guess?
        s = s.replace(".*", "").replace(".x", "")

        if s == "*":  # Match all versions.
            return cls(True, None, None, True)
        elif s.startswith(">="):
            return cls(
                True, Version.parse(s[2:], optional_minor_and_patch=True), None, True
            )
        elif s.startswith("<="):
            return cls(
                True, None, Version.parse(s[2:], optional_minor_and_patch=True), True
            )
        elif s.startswith(">"):
            return cls(
                False, Version.parse(s[1:], optional_minor_and_patch=True), None, True
            )
        elif s.startswith("<"):
            return cls(
                True, None, Version.parse(s[1:], optional_minor_and_patch=True), False
            )
        else:
            # There is no comparison operator. It's exactly this version number.
            try:
                v = Version.parse(s, optional_minor_and_patch=True)
                return cls(True, v, v, True)
            except ValueError as e:
                raise ValueError(f"Invalid version constraint: {s}") from e

    def __contains__(self, version: Version) -> bool:
        """Whether the interval contains version."""
        min_op = ge if self.min_inclusive else gt  # above the min
        max_op = le if self.max_inclusive else lt  # below the max
        return min_op(version, self.min) and max_op(version, self.max)

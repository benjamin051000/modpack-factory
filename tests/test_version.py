import pytest

from lib.version import Version, VersionInterval


@pytest.mark.parametrize(
    "s, contains_0, contains_1, contains_2",
    [
        (">1.0.0", False, False, True),
        (">=1.0.0", False, True, True),
        ("<1.0.0", True, False, False),
        ("<=1.0.0", True, True, False),
    ],
)
def test_version_interval_contains(
    s: str, contains_0: bool, contains_1: bool, contains_2: bool
):
    vi = VersionInterval.from_str(s)

    assert (Version.parse("0.9.0") in vi) == contains_0
    assert (Version.parse("1.0.0") in vi) == contains_1
    assert (Version.parse("2.0.0") in vi) == contains_2

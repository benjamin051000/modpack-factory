import pytest

from lib.toml.toml_constraint import MCVersion, MinecraftVersionConstraint


def test_mcversion_simple():
    assert MCVersion(1, 20, 1) < MCVersion(1, 21, 1)
    assert MCVersion(1, 20, 1) <= MCVersion(1, 21, 1)
    assert MCVersion(1, 20, 1) == MCVersion(1, 20, 1)
    assert MCVersion(1, 20, 1) > MCVersion(1, 20, 0)


def test_minecraftversionconstant_simple():
    v = MinecraftVersionConstraint.from_str("1.2.5")
    assert v.version == MCVersion(1, 2, 5)
    assert v.relationship is None

    # Test omitted zero
    v = MinecraftVersionConstraint.from_str("1.20")
    assert v.version == MCVersion(1, 20, 0)


def test_minecraftversionconstant_relationship():
    v = MinecraftVersionConstraint.from_str("==1.20.1")
    assert v.version == MCVersion(1, 20, 1)
    assert v.relationship == "=="

    v = MinecraftVersionConstraint.from_str("==1.20.0")
    assert v.version == MCVersion(1, 20, 0)

    v = MinecraftVersionConstraint.from_str(">=1.20.1")
    assert v.version == MCVersion(1, 20, 1)
    assert v.relationship == ">="


def test_minecraftversionconstant_bad_input():
    with pytest.raises(ValueError):
        MinecraftVersionConstraint.from_str("1.20.")

    with pytest.raises(ValueError):
        MinecraftVersionConstraint.from_str("=1.20.1")

    with pytest.raises(ValueError):
        MinecraftVersionConstraint.from_str("=<1.20.1")

    with pytest.raises(ValueError):
        MinecraftVersionConstraint.from_str("=>1.20.1")

    with pytest.raises(ValueError):
        MinecraftVersionConstraint.from_str("===1.20.1")

    with pytest.raises(ValueError):
        MinecraftVersionConstraint.from_str("<<1.20.1")

    with pytest.raises(ValueError):
        MinecraftVersionConstraint.from_str(">>1.20.1")

import pytest

from lib.mod.mod import Mod
from lib.sources.modrinth import Modrinth


@pytest.mark.skip
@pytest.mark.asyncio(loop_scope="session")
async def test_mod_from_modrinth(modrinth: Modrinth):
    sodium = await Mod.from_modrinth(modrinth, "sodium")

    assert sodium.slug == "sodium"


@pytest.mark.asyncio(loop_scope="session")
async def test_from_batched_simple(modrinth: Modrinth):
    # TODO this can be a dependency of some test_modrinth test
    slugs = ["sodium"]
    mods_json, versions_json = await modrinth.get_mods_batched(slugs)

    assert len(mods_json) == 1
    sodium = mods_json[0]
    assert sodium["slug"] == "sodium"
    assert sodium["id"] == "AANobbMI"

    mods = Mod.from_batched(mods_json, versions_json)
    assert len(mods) == len(slugs)

    for slug, mod in zip(slugs, mods, strict=True):
        assert mod.slug == slug
        assert len(mod.versions) >= 1


# TODO we can probably verify the batched constructors work AGAINST the original ones!
# Maybe try that?
# BUG this test is a false positive. Check the dependencies! (WIP below, now it fails)
@pytest.mark.asyncio(loop_scope="session")
async def test_from_batched_one_dependency(modrinth: Modrinth):
    # NOTE: Assumes test_get_mods_batched_one_dependency from test_modrinth passed.
    mods_json, versions_json = await modrinth.get_mods_batched(
        ["reeses-sodium-options"]
    )

    mods = Mod.from_batched(mods_json, versions_json)

    assert {mod.slug for mod in mods} == {
        "reeses-sodium-options",
        "sodium",
    }

    reeses_sodium_options = mods[0]
    assert reeses_sodium_options.slug == "reeses-sodium-options"

    # These versions have no dependencies listed on Modrinth,
    # even though they definitely do... Oops!
    quirky_versions = [
        "mc1.17.1-1.4.4",
        "mc1.16.5-1.4.7",
        "mc1.18.2-1.4.6",
        "mc1.16.5-1.4.1",
        "mc1.17.1-1.4.1",
        "mc1.18-1.2.3",
        "mc1.17.1-1.4.5",
        "mc1.18.2-1.4.5",
        "mc1.18.1-1.3.0",
        "mc1.18.1-1.4.0",
        "mc1.16.5-1.4.6",
        "mc1.18.2-1.4.2",
        "mc1.18.2-1.4.3",
        "mc1.17.1-1.3.0",
        "mc1.18.2-1.4.7",
        "mc1.16.5-1.4.5",
        "mc1.17.1-1.4.3",
        "1.2.1",
        "mc1.18.2-1.4.4",
        "mc1.17.1-1.4.6",
        "mc1.16.5-1.3.0",
        "mc1.16.5-1.4.2",
        "mc1.16.5-1.4.3",
        "mc1.18.2-1.4.1",
        "mc1.18.1-1.2.4",
        "mc1.19-1.4.3",
        "mc1.19.2-1.4.6",
        "mc1.19.2-1.4.7",
        "mc1.16.5-1.4.4",
        "mc1.17.1-1.2.3",
        "mc1.16.5-1.4.0",
        "mc1.19-1.4.4",
        "mc1.17.1-1.4.7",
        "mc1.17.1-1.4.2",
        "mc1.17.1-1.2.2",
        "mc1.17.1-1.4.0",
        "1.2.0",
        "mc1.19.2-1.4.5",
        "25",
    ]

    for version in reeses_sodium_options.versions:
        if version.version_number not in quirky_versions:
            assert len(version.dependencies) == 1
            # Horrible!
            dep = next(iter(version.dependencies.values())).pop()
            assert dep.mod_slug == "sodium"

    # Test case: mc1.17.1-1.4.4 has 0 deps
    # So does mc1.16.5-1.4.7

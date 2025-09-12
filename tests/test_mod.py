import pytest

from lib.mod.mod import Mod


@pytest.mark.skip
@pytest.mark.asyncio(loop_scope="session")
async def test_mod_from_modrinth(modrinth):
    sodium = await Mod.from_modrinth(modrinth, "sodium")

    assert sodium.slug == "sodium"


@pytest.mark.asyncio(loop_scope="session")
async def test_from_batched_simple(modrinth):
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
async def test_from_batched_one_dependency(modrinth):
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

    # Test case: mc1.17.1-1.4.4 has 0 deps

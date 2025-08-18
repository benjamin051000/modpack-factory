import pytest

from lib.mod.mod import Mod


@pytest.mark.asyncio(loop_scope="session")
async def test_mod_from_modrinth(modrinth):
    sodium = await Mod.from_modrinth(modrinth, "sodium")

    assert sodium.slug == "sodium"


@pytest.mark.asyncio(loop_scope="session")
async def test_from_batched_simple(modrinth):
    mods_json, versions_json = await modrinth.get_mods_batched(["sodium"])

    assert len(mods_json) == 1
    sodium = mods_json[0]
    assert sodium["slug"] == "sodium"
    assert sodium["id"] == "AANobbMI"

    mods = Mod.from_batched(mods_json, versions_json)
    assert len(mods) == 1

    sodium = mods[0]
    assert sodium.slug == "sodium"
    assert len(sodium.versions) >= 1


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

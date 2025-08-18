import aiohttp
import pytest

from lib.mod.mod import Mod, get_mods_batched
from lib.sources.modrinth import API


@pytest.mark.asyncio
async def test_mod_from_modrinth():
    async with aiohttp.ClientSession(API) as session:
        sodium = await Mod.from_modrinth(session, "sodium")

    assert sodium.slug == "sodium"


@pytest.mark.asyncio
async def test_from_batched_simple():
    async with aiohttp.ClientSession(API) as session:
        mods_json, versions_json = await get_mods_batched(session, ["sodium"])

    assert len(mods_json) == 1
    sodium = mods_json[0]
    assert sodium["slug"] == "sodium"
    assert sodium["id"] == "AANobbMI"

    mods = Mod.from_batched(mods_json, versions_json)
    assert len(mods) == 1

    sodium = mods[0]
    assert sodium.slug == "sodium"
    assert len(sodium.versions) >= 1


@pytest.mark.asyncio
async def test_from_batched_one_dependency():
    # NOTE: Assumes test_get_mods_batched_one_dependency from test_modrinth passed.
    async with aiohttp.ClientSession(API) as session:
        mods_json, versions_json = await get_mods_batched(
            session, ["reeses-sodium-options"]
        )

    mods = Mod.from_batched(mods_json, versions_json)
    assert {mod.slug for mod in mods} == {
        "reeses-sodium-options",
        "sodium",
    }

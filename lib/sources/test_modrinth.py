import aiohttp
import pytest

from lib.mod.mod import get_mods_batched
from lib.sources.modrinth import API, get_versions


@pytest.mark.asyncio
async def test_get_project_async():
    async with aiohttp.ClientSession(API).get("project/sodium") as response:
        json = await response.json()

    assert json["slug"] == "sodium"


@pytest.mark.asyncio
async def test_get_versions():
    # Obtained from the API/project/sodium "versions" info
    project_id = "AANobbMI"
    sodium_releases = ["yaoBL9D9", "YAGZ1cCS", "1b0GhKHj"]
    async with aiohttp.ClientSession(API) as session:
        versions = await get_versions(session, sodium_releases)

    assert len(versions) == 3
    for version in versions:
        assert version["project_id"] == project_id
        for key in ["dependencies", "files", "game_versions", "id", "loaders", "name"]:
            assert key in version


@pytest.mark.asyncio
async def test_get_mods_batched_simple():
    async with aiohttp.ClientSession(API) as session:
        mods_json, versions_json = await get_mods_batched(session, ["sodium"])

    assert len(mods_json) == 1
    sodium = mods_json[0]
    assert sodium["slug"] == "sodium"
    assert sodium["id"] == "AANobbMI"


@pytest.mark.asyncio
async def test_get_mods_batched_one_dependency():
    async with aiohttp.ClientSession(API) as session:
        mods_json, versions_json = await get_mods_batched(
            session, ["reeses-sodium-options"]
        )

    assert len(mods_json) == 2

    reeses, sodium = mods_json

    assert reeses["slug"] == "reeses-sodium-options"
    assert reeses["id"] == "Bh37bMuy"

    assert sodium["slug"] == "sodium"
    assert sodium["id"] == "AANobbMI"
    # with open("reeses.json", "w") as f:
    #     json.dump(mods_json, f)


@pytest.mark.asyncio
async def test_get_mods_batched_multiple_dependencies():
    async with aiohttp.ClientSession(API) as session:
        mods_json, versions_json = await get_mods_batched(session, ["createaddition"])
    assert {mod["slug"] for mod in mods_json} == {
        "createaddition",
        "create",
        "create-fabric",
        "flywheel",
        "fabric-api",
    }
    # with open("createaddition.json", "w") as f:
    #     json.dump(mods_json, f)

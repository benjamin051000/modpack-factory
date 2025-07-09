import aiohttp
import pytest

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

from io import BytesIO
from zipfile import ZipFile

import pytest
from aiohttp import ClientSession
from aiolimiter import AsyncLimiter

from lib.sources.modrinth import Modrinth


@pytest.mark.asyncio(loop_scope="session")
async def test_raw_api(
    aiohttp_session: ClientSession, modrinth_rate_limiter: AsyncLimiter
):
    """A simple test of the actual API endpoint.
    If this fails, basically everything else will too."""

    async with (
        modrinth_rate_limiter,
        aiohttp_session.get("project/sodium") as response,
    ):
        json = await response.json()

    assert json["slug"] == "sodium"


@pytest.mark.asyncio(loop_scope="session")
async def test_get_versions_sodium(modrinth: Modrinth):
    """Test versions endpoint against known values."""
    # Obtained from the API/project/sodium "versions" info
    project_id = "AANobbMI"
    sodium_releases = ["yaoBL9D9", "YAGZ1cCS", "1b0GhKHj"]
    versions: list = await modrinth.get_versions(sodium_releases)

    assert len(versions) == 3
    for version in versions:
        assert version["project_id"] == project_id
        for key in ["dependencies", "files", "game_versions", "id", "loaders", "name"]:
            assert key in version


@pytest.mark.asyncio(loop_scope="session")
async def test_get_mods_batched_simple(modrinth: Modrinth):
    """Test the batched function that gets mod and version JSON."""
    mods_json, versions_json = await modrinth.get_mods_batched(["sodium"])

    assert len(mods_json) == 1
    sodium = mods_json[0]
    assert sodium["slug"] == "sodium"
    assert sodium["id"] == "AANobbMI"
    assert len(versions_json) >= 1


@pytest.mark.asyncio(loop_scope="session")
async def test_get_mods_batched_one_dependency(modrinth: Modrinth):
    mods_json, versions_json = await modrinth.get_mods_batched(
        ["reeses-sodium-options"]
    )

    assert len(mods_json) == 2

    reeses, sodium = mods_json

    assert reeses["slug"] == "reeses-sodium-options"
    assert reeses["id"] == "Bh37bMuy"

    assert sodium["slug"] == "sodium"
    assert sodium["id"] == "AANobbMI"

    # There should be at least 1 version per mod
    assert len(versions_json) >= len(mods_json)


@pytest.mark.asyncio(loop_scope="session")
async def test_get_mods_batched_multiple_dependencies(modrinth: Modrinth):
    mods_json, versions_json = await modrinth.get_mods_batched(["createaddition"])

    all_mods = {
        "createaddition",
        "create",
        "create-fabric",
        "flywheel",
        "fabric-api",
    }

    assert {mod["slug"] for mod in mods_json} == all_mods

    assert len(versions_json) >= len(all_mods)


@pytest.mark.asyncio(loop_scope="session")
async def test_download(modrinth: Modrinth):
    url = "https://cdn.modrinth.com/data/AANobbMI/versions/ND4ROcMQ/sodium-fabric-0.6.13%2Bmc1.21.6.jar"

    with BytesIO() as file:
        await modrinth.download(url, file)

        with ZipFile(file) as zf:
            # There should be many files in the .jar
            assert len(zf.infolist()) >= 1

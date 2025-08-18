import pytest


@pytest.mark.asyncio(loop_scope="session")
async def test_get_project_async(aiohttp_session, modrinth_rate_limiter):
    async with (
        modrinth_rate_limiter,
        aiohttp_session.get("project/sodium") as response,
    ):
        json = await response.json()

    assert json["slug"] == "sodium"


@pytest.mark.asyncio(loop_scope="session")
async def test_get_versions(modrinth):
    # Obtained from the API/project/sodium "versions" info
    project_id = "AANobbMI"
    sodium_releases = ["yaoBL9D9", "YAGZ1cCS", "1b0GhKHj"]
    versions = await modrinth.get_versions(sodium_releases)

    assert len(versions) == 3
    for version in versions:
        assert version["project_id"] == project_id
        for key in ["dependencies", "files", "game_versions", "id", "loaders", "name"]:
            assert key in version


@pytest.mark.asyncio(loop_scope="session")
async def test_get_mods_batched_simple(modrinth):
    mods_json, versions_json = await modrinth.get_mods_batched(["sodium"])

    assert len(mods_json) == 1
    sodium = mods_json[0]
    assert sodium["slug"] == "sodium"
    assert sodium["id"] == "AANobbMI"
    assert len(versions_json) >= 1


@pytest.mark.asyncio(loop_scope="session")
async def test_get_mods_batched_one_dependency(modrinth):
    mods_json, versions_json = await modrinth.get_mods_batched(
        ["reeses-sodium-options"]
    )

    assert len(mods_json) == 2

    reeses, sodium = mods_json

    assert reeses["slug"] == "reeses-sodium-options"
    assert reeses["id"] == "Bh37bMuy"

    assert sodium["slug"] == "sodium"
    assert sodium["id"] == "AANobbMI"
    # with open("reeses.json", "w") as f:
    #     json.dump(mods_json, f)


@pytest.mark.asyncio(loop_scope="session")
async def test_get_mods_batched_multiple_dependencies(modrinth):
    mods_json, versions_json = await modrinth.get_mods_batched(["createaddition"])
    assert {mod["slug"] for mod in mods_json} == {
        "createaddition",
        "create",
        "create-fabric",
        "flywheel",
        "fabric-api",
    }
    assert len(versions_json) >= 1
    # with open("createaddition.json", "w") as f:
    #     json.dump(mods_json, f)

import pytest

from lib.jar import FabricJarConstraints
from lib.mod.mod import Mod
from lib.sources.modrinth import Modrinth


def test_from_modrinth_json():
    slug = "sodium"
    sodium_json = {
        "game_versions": ["1.21.6", "1.21.7", "1.21.8"],
        "loaders": ["neoforge"],
        "id": "lgWRGiHv",
        "project_id": "AANobbMI",
        "author_id": "DzLrfrbK",
        "featured": "false",
        "name": "Sodium 0.7.2 for NeoForge 1.21.8",
        "version_number": "mc1.21.8-0.7.2-neoforge",
        "changelog": "- Improved the appearance of mipmaps when viewed at extreme...",
        "changelog_url": "null",
        "date_published": "2025-10-09T20:38:08.684095Z",
        "downloads": 14732,
        "version_type": "release",
        "status": "listed",
        "requested_status": "null",
        "files": [
            {
                "hashes": {
                    "sha512": "601a1da59945655048d66dc9cfc1a2a386c587074e7f707a7c0d9034940a87bf2e628c0b5fab708eaeeaeb01d8b82f5b2cb016f5867e2bf766a1f081ac75ef03",  # noqa: E501
                    "sha1": "e66282d85ed0d769f3ec602297f0110e36e88c35",
                },
                "url": "https://cdn.modrinth.com/data/AANobbMI/versions/lgWRGiHv/sodium-neoforge-0.7.2%2Bmc1.21.8.jar",
                "filename": "sodium-neoforge-0.7.2+mc1.21.8.jar",
                "primary": "true",
                "size": 1253306,
                "file_type": "null",
            }
        ],
        "dependencies": [],
    }
    mod = Mod.from_modrinth_json(slug, sodium_json, set())
    assert mod.slug == slug
    assert mod.project_id == sodium_json["project_id"]
    for version in mod.game_versions:
        assert str(version) in sodium_json["game_versions"]
    assert len(mod.files) >= 1


@pytest.mark.asyncio(loop_scope="session")
async def test_from_batched_simple(modrinth: Modrinth):
    # TODO this can be a dependency of some test_modrinth test
    slugs = ["sodium"]
    mods_json, versions_json = await modrinth.get_mods_batched(slugs)

    assert len(mods_json) == 1
    sodium = mods_json[0]
    assert sodium["slug"] == "sodium"
    assert sodium["id"] == "AANobbMI"

    constraints = await FabricJarConstraints.from_modrinth_batched(
        modrinth, versions_json
    )
    mods = Mod.from_batched(modrinth, mods_json, versions_json, constraints)

    # There should be at least one Mod per slug. Likely far more.
    assert len(mods) >= len(slugs)


# TODO we can probably verify the batched constructors work AGAINST the original ones!
# Maybe try that?
# BUG this test is a false positive. Check the dependencies! (WIP below, now it fails)
@pytest.mark.asyncio(loop_scope="session")
async def test_from_batched_one_dependency(modrinth: Modrinth):
    # NOTE: Assumes test_get_mods_batched_one_dependency from test_modrinth passed.
    mods_json, versions_json = await modrinth.get_mods_batched(
        ["reeses-sodium-options"]
    )

    constraints = await FabricJarConstraints.from_modrinth_batched(
        modrinth, versions_json
    )
    mods = Mod.from_batched(modrinth, mods_json, versions_json, constraints)

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

import pytest
from semver import Version

from lib.jar import FabricJarConstraints
from lib.sources.modrinth import Modrinth

mock_json = {
    "schemaVersion": 1,
    "id": "sodium",
    "version": "0.5.0",
    "name": "Sodium",
    "description": "Sodium is a...",
    "authors": ["JellySquid"],
    "contact": {
        "homepage": "https://github.com/CaffeineMC/sodium-fabric",
        "sources": "https://github.com/CaffeineMC/sodium-fabric",
        "issues": "https://github.com/CaffeineMC/sodium-fabric/issues",
    },
    "license": "LGPL-3.0-only",
    "icon": "assets/sodium/icon.png",
    "environment": "client",
    "entrypoints": {},
    "custom": {},
    "depends": {
        "fabricloader": ">=0.12.0",
        "fabric-rendering-data-attachment-v1": ">=0.1",
        "fabric-rendering-fluids-v1": ">=0.1",
    },
    "breaks": {"optifabric": "*", "canvas": "*", "notenoughcrashes": "*"},
}


def test_from_json():
    constraints = FabricJarConstraints._from_json(mock_json)

    assert constraints.id == "sodium"
    assert constraints.version == "0.5.0"

    assert len(constraints.depends) == 3
    assert constraints.depends[0].operand == "fabricloader"
    assert constraints.depends[0].operators[0]._s == ">=0.12.0"
    assert Version(0, 12, 0) in constraints.depends[0]
    assert Version(0, 1, 0) not in constraints.depends[0]

    assert len(constraints.breaks) == 3
    assert constraints.breaks[0].operand == "optifabric"
    assert constraints.breaks[0].operators[0]._s == "*"
    assert Version(0, 12, 0) in constraints.breaks[0]
    assert Version(0, 1, 0) in constraints.breaks[0]

    assert len(constraints.recommends) == 0
    assert len(constraints.suggests) == 0
    assert len(constraints.conflicts) == 0


@pytest.mark.asyncio(loop_scope="session")
async def test_from_modrinth(modrinth: Modrinth):
    url = "https://cdn.modrinth.com/data/AANobbMI/versions/ND4ROcMQ/sodium-fabric-0.6.13%2Bmc1.21.6.jar"
    constraints = await FabricJarConstraints.from_modrinth(modrinth, url)

    correct_depends = {
        "fabric-block-view-api-v2": "*",
        "fabric-renderer-api-v1": "*",
        "fabric-rendering-fluids-v1": ">=2.0.0",
        "fabric-resource-loader-v0": "*",
        "fabricloader": ">=0.16.0",
    }

    assert constraints.id == "sodium"
    # HACK: See FabricJarConstraints._from_json(), we also do this string replace there.
    # This should match that.
    assert constraints.version == Version(0, 6, 13, build="mc1.21.6")
    correct_depends_names = set(correct_depends.keys())
    constraint_depends_names = set(dep.operand for dep in constraints.depends)
    assert correct_depends_names == constraint_depends_names

    correct_breaks = {
        "betterend": "<=21.0.11",
        "betterfpsdist": "<=1.21-4.5",
        "bobby": "<5.2.4",
        "canvas": "*",
        "chunksfadein": "<2.0.2-1.21.2",
        "cull-less-leaves": "<=1.3.0",
        "cullleaves": "<=3.4.0-fabric",
        "custom_hud": "<3.4.2",
        "embeddium": "*",
        "farsight": "<=1.21-4.3",
        "iceberg": "<1.2.7",
        "iris": "<1.8.7",
        "moreculling": "<1.2.4",
        "movingelevators": "<=1.4.7",
        "notenoughcrashes": "<4.4.8",
        "noxesium": "<2.3.3",
        "ocrenderfix_sodium": "*",
        "optifabric": "*",
        "reeses-sodium-options": "<1.8.0",
        "simply-no-shading": "<7.6.2",
        "sodium-blendingregistry": "*",
        "sodium-extra": "<0.6.0",
        "sspb": "<4.0.0",
        "vulkanmod": "*",
    }

    correct_breaks_names = set(correct_breaks.keys())
    constraint_breaks_names = set(dep.operand for dep in constraints.breaks)
    assert correct_breaks_names == constraint_breaks_names

    # TODO I'm not sure what "provides" does but may be worth testing later.
    # correct_provides = ["indium"]


@pytest.mark.asyncio(loop_scope="session")
async def test_from_modrinth_batched(modrinth: Modrinth):
    # TODO pick something with less versions than sodium.
    # We download every jar of it and it takes forever lol
    # sodium does not depend on anything, according to Modrinth's website...
    _, versions_json = await modrinth.get_mods_batched(["sodium"])

    constraints = await FabricJarConstraints.from_modrinth_batched(
        modrinth, versions_json
    )

    # But it turns out, every version of sodium has dependencies!
    # TODO when ready to add non-fabric, remove this if
    ids = [v["id"] for v in versions_json if v["loaders"] == ["fabric"]]
    for id in ids:
        constraint = constraints[id]
        jar_constraints = list(constraint.values())
        for jar_constraint in jar_constraints:
            fjc = jar_constraint.result()
            assert len(fjc.depends) >= 1

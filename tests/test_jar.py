from lib.jar.extract import FabricJarConstraints

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

    assert len(constraints.depends) == 3
    assert constraints.depends[0].operand == "fabricloader"
    assert constraints.depends[0].operator == ">=0.12.0"

    assert len(constraints.breaks) == 3
    assert constraints.breaks[0].operand == "optifabric"
    assert constraints.breaks[0].operator == "*"

    assert len(constraints.recommends) == 0
    assert len(constraints.suggests) == 0
    assert len(constraints.conflicts) == 0

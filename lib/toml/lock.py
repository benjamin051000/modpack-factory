from pathlib import Path

import tomlkit

from lib.mod.mod import ModVersion
from lib.toml.toml_constraint import MCVersion

FILENAME = "modpack.lock"


def write_lockfile(toml: tomlkit.TOMLDocument, filename: Path):
    with open(filename, "w") as f:
        tomlkit.dump(toml, f)
    print(f"{filename} created.")


# def read_lockfile(filename: Path) -> tomlkit.TOMLDocument:
#     with open(filename) as f:
#         return tomlkit.load(f)


def lock(mc_version: MCVersion, mods: list[ModVersion]) -> tomlkit.TOMLDocument:
    """Generate the locked TOML."""
    doc = tomlkit.document()
    doc.add("minecraft-version", str(mc_version))
    for mod in mods:
        aot = tomlkit.aot()
        aot.append(
            tomlkit.item(
                {
                    "slug": mod.slug,
                    "version_number": mod.version_number,
                    "url": next(
                        file.url
                        for file in mod.files
                        if file.primary or len(mod.files) == 1
                    ),
                }
            )
        )
        doc.append("mod", aot)

    return doc

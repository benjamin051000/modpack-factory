from pathlib import Path
import zipfile
import json


# TODO eventually we will want to look at neo/forge as well.
# We need to pass the Version info collected from Modrinth versions API
# which explains which loaders work with this jar. Then, we just have a
# dict that maps loader name to the file it uses for metadata.


def extract_fabric(path: Path) -> dict:
    """Extracts data from fabric.mod.json, found in Fabric mod .jar files."""
    with zipfile.ZipFile(path) as archive:
        data: dict = json.loads(archive.read("fabric.mod.json"))
    return data


if __name__ == "__main__":
    extract_fabric(Path("iris-neoforge-1.8.11+mc1.21.5.jar"))

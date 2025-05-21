from json import JSONDecodeError
import sys
import aiohttp
import requests
from pathlib import Path

API = "https://api.modrinth.com/v2/"

# TODO make this into a subclass so we can dispatch to the appropriate one once curseforge is added.


def search(query: str) -> dict:
    response = requests.get(f"{API}/search", params={"query": query})
    return response.json()


def get_project(slug: str) -> dict:
    try:
        return requests.get(f"{API}/project/{slug}").json()
    except JSONDecodeError:
        print(f"Error: Mod '{slug}' not found.", file=sys.stderr)
        sys.exit(1)


def get_projects(slugs: list[str]) -> dict:
    formatted_slugs = str(slugs).replace("'", '"')  # API requires double-quotes
    return requests.get(f"{API}/projects", params={"ids": formatted_slugs}).json()


async def get_versions(session: aiohttp.ClientSession, slug: str) -> dict:
    async with session.get(f"project/{slug}/version") as response:
        return await response.json()


def download_jar(url: str, filename: Path):
    response = requests.get(url, stream=True)
    with open(filename, "wb") as f:
        for chunk in response.iter_content(chunk_size=10 * 1024):  # 10kb
            f.write(chunk)

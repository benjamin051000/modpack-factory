import asyncio
import sys
from itertools import batched
from pathlib import Path

import aiohttp
import requests
from aiolimiter import AsyncLimiter

MODRINTH_API = "https://api.modrinth.com/v2/"


# The Modrinth docs state that modrinth rate limits at 300 requests per minute.
RATE_LIMIT_PER_MIN = 300

# I was told by a SWE @ Modrinth that 800 is generally the
# limit Cloudflare allows. So, batch in 800s.
HTTP_PARAMS_BATCH_LIMIT = 800

# TODO make this into a subclass so we can dispatch to
# the appropriate one once curseforge is added.


class Modrinth:
    def __init__(
        self, session: aiohttp.ClientSession, limiter: AsyncLimiter | None = None
    ) -> None:
        self.session = session

        if limiter is None:
            limiter = AsyncLimiter(RATE_LIMIT_PER_MIN)
        self.limiter = limiter

    async def search(self, query: str) -> dict:
        async with (
            self.limiter,
            self.session.get("search", params={"query": query}) as response,
        ):
            return await response.json()

    async def get_project(self, slug_or_id: str) -> dict:
        async with self.limiter, self.session.get(f"project/{slug_or_id}") as response:
            # TODO JSONDecodeError?
            return await response.json()

    async def get_projects(self, slugs: list[str]) -> list[dict]:
        formatted_slugs = str(slugs).replace("'", '"')  # API requires double-quotes
        # NOTE: This API skips ones that don't exist.
        async with (
            self.limiter,
            self.session.get("projects", params={"ids": formatted_slugs}) as response,
        ):
            return await response.json()

    async def get_version(self, slug: str) -> list:
        async with (
            self.limiter,
            self.session.get(f"project/{slug}/version") as response,
        ):
            versions_json = await response.json()

        # Filter out versions which only run on a Minecraft snapshot.
        # Remove snapshots for now.
        for version in versions_json:
            version["game_versions"] = [
                v
                for v in version["game_versions"]
                # Skip snapshots, pre-releases, RCs, beta versions.
                # Sourced from modrith web filter
                if not any(
                    c in v for c in ["w", "-pre", "-rc", "b", "a", "c", "rd-", "inf-"]
                )
            ]

        # Versions which only supported snapshots now have empty game_versions fields.
        filtered_versions_json = [v for v in versions_json if len(v["game_versions"])]

        return filtered_versions_json

    async def get_versions(self, version_ids: list[str]) -> list:
        formatted_ids = str(version_ids).replace("'", '"')
        async with (
            self.limiter,
            self.session.get("versions", params={"ids": formatted_ids}) as response,
        ):
            try:
                versions: list = await response.json()
            except aiohttp.ContentTypeError:
                text_response = await response.text()
                print(text_response, file=sys.stderr)
                sys.exit(1)
        return versions

    # TODO decorate get_versions and get_project_async
    async def get_versions_batched(self, version_ids: list[str]) -> list:
        tasks = [
            self.get_versions(list(batch))
            for batch in batched(version_ids, HTTP_PARAMS_BATCH_LIMIT, strict=False)
        ]

        results = await asyncio.gather(*tasks)
        return [item for result in results for item in result]

    # TODO verify this handles circular dependencies
    # (although I'd be surprised if any exist)
    async def get_mods_batched(self, slugs: list[str]) -> tuple[list[dict], list[dict]]:
        """Use the batching APIs to get a list of mods (including recursive
        dependencies) and versions in JSON form."""
        # all mods in JSON form
        all_mods = []
        # all versions in JSON form.
        all_versions = []

        # Start with the top-level mods. This gets rewritten in the loop
        mod_names: list[str] = slugs

        while mod_names:
            mods_json = await self.get_projects(mod_names)
            all_mods.extend(mods_json)

            # all versions in slug form
            version_names = [ver for mod in mods_json for ver in mod["versions"]]

            versions_json = await self.get_versions_batched(version_names)

            # Filter to only required dependencies (filter out, e.g., "incompatible",
            # see https://modrinth.com/mod/sodium/version/mc1.20.1-0.5.0)
            for version in versions_json:
                version["dependencies"] = [
                    dep
                    for dep in version["dependencies"]
                    if dep["dependency_type"] == "required"
                ]

            all_versions.extend(versions_json)

            # Now, get the dependencies
            dependencies = [
                dep
                for version_json in versions_json
                for dep in version_json["dependencies"]
            ]

            # There are no more dependencies to collect. We're done.
            if not dependencies:
                break

            required_dependencies_ids = [dep["project_id"] for dep in dependencies]
            # This is the new set of mods to get
            mod_names = required_dependencies_ids

        return all_mods, all_versions


def download_jar(url: str, filename: Path):
    response = requests.get(url, stream=True)
    with open(filename, "wb") as f:
        for chunk in response.iter_content(chunk_size=10 * 1024):  # 10kb
            f.write(chunk)

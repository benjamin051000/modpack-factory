import asyncio
import sqlite3
import sys
from itertools import batched
from typing import BinaryIO

import aiohttp
from aiolimiter import AsyncLimiter

MODRINTH_API = "https://api.modrinth.com/v2/"


# The Modrinth docs state that modrinth rate limits at 300 requests per minute.
RATE_LIMIT_PER_MIN = 300

# I was told by a SWE @ Modrinth that 800 is generally the
# limit Cloudflare allows. So, batch in 800s.
HTTP_PARAMS_BATCH_LIMIT = 800

# TODO make this into a subclass so we can dispatch to
# the appropriate one once curseforge is added.


# TODO is this a good chunk size?
CHUNKSIZE = 100 * 1024  # 100KB
"""Chunk size for downloading files."""


class Modrinth:
    def __init__(
        self,
        session: aiohttp.ClientSession,
        conn: sqlite3.Connection,
        limiter: AsyncLimiter | None = None,
    ) -> None:
        self.session = session
        self.conn = conn
        self.cursor = self.conn.cursor()

        if limiter is None:
            limiter = AsyncLimiter(RATE_LIMIT_PER_MIN)
        self.limiter = limiter

    async def search(self, query: str, limit: int | None = None) -> dict:
        params = {"query": query}
        if limit:
            params["limit"] = str(limit)

        async with (
            self.limiter,
            self.session.get("search", params=params) as response,
        ):
            try:
                return await response.json()
            except aiohttp.ContentTypeError:
                text_response = await response.text()
                print(text_response, file=sys.stderr)
                sys.exit(1)

    async def get_project(self, slug_or_id: str) -> dict:
        async with self.limiter, self.session.get(f"project/{slug_or_id}") as response:
            # TODO JSONDecodeError?
            return await response.json()

    # TODO use the HTTP_PARAMS_BATCH_LIMIT here, too, just in case
    async def get_projects(self, slugs: list[str]) -> list[dict]:
        formatted_slugs = str(slugs).replace("'", '"')  # API requires double-quotes
        # NOTE: This API skips ones that don't exist.
        async with (
            self.limiter,
            self.session.get("projects", params={"ids": formatted_slugs}) as response,
        ):
            try:
                return await response.json()
            except aiohttp.ContentTypeError:
                print(await response.text())
                raise
                # sys.exit(1)

    async def get_version(self, slug: str) -> list:
        async with (
            self.limiter,
            self.session.get(f"project/{slug}/version") as response,
        ):
            versions_json = await response.json()

        return versions_json

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

        # TODO consider a TaskGroup?
        results = await asyncio.gather(*tasks)
        return self._filter_unsupported_versions(
            [item for result in results for item in result]
        )

    # TODO verify this handles circular dependencies
    # (although I'd be surprised if any exist)
    async def get_mods_batched(self, slugs: list[str]) -> tuple[list[dict], list[dict]]:
        """Use the batching APIs to get a list of mods (including recursive
        dependencies) and versions in JSON form."""
        # all mods in JSON form
        all_mods: list[dict] = []
        # all versions in JSON form.
        all_versions: list[dict] = []

        # Keep track of entries to avoid duplicates.
        all_mod_ids: set[str] = set()
        all_version_names: set[str] = set()

        # Start with the top-level mods. This gets rewritten in the loop
        # TODO set()? See how it's updated below
        mod_names: list[str] = slugs

        while mod_names:
            mods_json: list = await self.get_projects(mod_names)
            all_mods.extend(mod for mod in mods_json if mod["id"] not in all_mod_ids)
            all_mod_ids.update(mod["id"] for mod in mods_json)

            # all versions in slug form
            version_names: list[str] = [
                ver
                for mod in mods_json
                for ver in mod["versions"]
                if ver not in all_version_names
            ]

            versions_json = await self.get_versions_batched(version_names)

            # Filter to only required dependencies (filter out, e.g., "incompatible",
            # see https://modrinth.com/mod/sodium/version/mc1.20.1-0.5.0
            for version in versions_json:
                # NOTE: This modifies elements in versions_json.
                version["dependencies"] = [
                    dep
                    for dep in version["dependencies"]
                    if dep["dependency_type"] == "required"
                ]

            all_versions.extend(versions_json)
            assert len(version_names) == len(set(version_names))
            all_version_names.update(version_names)

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
            # NOTE I am removing duplicates here, for better or worse...
            mod_names = list(set(required_dependencies_ids))

        # Check that there are no duplicates.
        # Use the id field, which is the UUID for each version/mod.
        # WARNING: asserts are not always checked!
        assert len(all_versions) == len({v["id"] for v in all_versions})
        assert len(all_mods) == len({m["id"] for m in all_mods})

        return all_mods, all_versions

    async def download(self, url: str, file: BinaryIO) -> bool:
        """Download a release file (AKA a .jar file)."""
        # First, check if it's in the database.
        try:
            result = self.cursor.execute(
                "SELECT url FROM mods WHERE url=?", (url,)
            ).fetchone()
            if result:
                # We've already got it downloaded. Do nothing.
                return False
        except sqlite3.OperationalError:
            # No worries, for now just download it normally
            pass

        # NOTE: No self.limiter here. This is a CDN so we can blast it, apparently.
        async with self.session.get(url) as response:
            async for chunk in response.content.iter_chunked(CHUNKSIZE):
                file.write(chunk)
        return True

    @staticmethod
    def _filter_unsupported_versions(raw_versions_json: list[dict]) -> list[dict]:
        name = raw_versions_json[0]["name"]
        print(f"HACK: Filtering unsupported versions for {name}...")

        # HACK currently, unsupported entries are
        # - forge, neoforge
        # - optional dependencies
        # - snapshots, pre-releases, RCs, beta versions of minecraft.
        def is_forge(version_json: dict) -> bool:
            # HACK: Skip non-fabric until we have more Jar Constraints representations.
            # TODO remove this when we're ready for Forge and others.
            return set(version_json["loaders"]) - {"forge", "neoforge"} == set()

        def is_unsupported_release(version_json: dict) -> bool:
            # Skip snapshots, pre-releases, RCs, beta versions.
            # Sourced from modrith web filter
            kw_substring = {"w", "-pre", "-rc", "b", "a", "c", "rd-", "inf-"}
            return any(
                keyword in version
                for keyword in kw_substring
                for version in version_json["game_versions"]
            )

        new = [
            version
            for version in raw_versions_json
            if not any([is_forge(version), is_unsupported_release(version)])
        ]

        diff = len(raw_versions_json) - len(new)

        print(f"{diff} (out of {len(raw_versions_json)}) versions filtered.")
        return new

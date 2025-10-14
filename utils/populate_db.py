"""
Create and populate the database.
"""

import asyncio
import sqlite3
from io import BytesIO

from aiohttp import ClientSession, ClientTimeout
from tqdm.asyncio import tqdm, tqdm_asyncio

from lib.sources.modrinth import MODRINTH_API, Modrinth

DB_NAME = "mods.db"

MOD_LIMIT = 50


async def download_task(
    conn: sqlite3.Connection,
    cursor: sqlite3.Cursor,
    modrinth: Modrinth,
    pbar: tqdm_asyncio,
    sha512: str,
    name: str,
    url: str,
) -> None:
    with BytesIO() as f:
        if not await modrinth.download(url, f):
            pbar.update(1)
            return

        try:
            cursor.execute(
                "INSERT INTO mods VALUES (?, ?, ?, ?)",
                (sha512, name, url, f.getvalue()),
            )
        except sqlite3.IntegrityError as e:
            # NOTE: Ran into this with ferrite-core 6.0.0 & 7.0.0,
            # where multiple version entries referenced files with exactly
            # the same sha512. Modrinth team told me this was a mistake and to
            # raise a ticket.
            if e.sqlite_errorname == "SQLITE_CONSTRAINT_PRIMARYKEY":
                print(f'"{name}" appears to have a duplicate db entry, skipping.')
                print(f"sha512: {sha512}")
                pass
            else:
                raise

        conn.commit()
    pbar.update(1)


async def main():
    with sqlite3.connect(DB_NAME) as conn:
        cursor = conn.cursor()

        cursor.execute("""
            CREATE TABLE IF NOT EXISTS mods (
                sha512 PRIMARY KEY,
                name,
                url,
                jar
            )
        """)
        # name is the name of the file
        async with ClientSession(
            MODRINTH_API, timeout=ClientTimeout(60 * 10)
        ) as session:
            modrinth = Modrinth(session, conn)

            # Get the 100 top mods
            slugs = [
                j["slug"] for j in (await modrinth.search("", limit=MOD_LIMIT))["hits"]
            ]
            _, versions_json = await modrinth.get_mods_batched(slugs)

            print(f"num mods to download: {len(versions_json)}")

            # TODO progress?
            all_items = [
                (
                    f["hashes"]["sha512"],
                    f["filename"],
                    f["url"],
                )
                for v in versions_json
                for f in v["files"]
            ]
            with tqdm(total=len(all_items)) as pbar:
                async with asyncio.TaskGroup() as tg:
                    _ = [
                        tg.create_task(
                            download_task(conn, cursor, modrinth, pbar, *items)
                        )
                        for items in all_items
                    ]


if __name__ == "__main__":
    asyncio.run(main())

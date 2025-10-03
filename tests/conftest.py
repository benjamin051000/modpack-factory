import sqlite3

import pytest
import pytest_asyncio
from aiohttp import ClientSession
from aiolimiter import AsyncLimiter

from lib.sources.modrinth import MODRINTH_API, RATE_LIMIT_PER_MIN, Modrinth


@pytest_asyncio.fixture(scope="session", loop_scope="session")
async def aiohttp_session():
    async with ClientSession(MODRINTH_API) as session:
        yield session


@pytest.fixture(scope="session")
def modrinth_rate_limiter() -> AsyncLimiter:
    return AsyncLimiter(RATE_LIMIT_PER_MIN)


@pytest.fixture(scope="session")
def db_conn():
    with sqlite3.connect("test_mods.db") as conn:
        yield conn


@pytest_asyncio.fixture(scope="session", loop_scope="session")
async def modrinth(
    aiohttp_session: ClientSession,
    db_conn: sqlite3.Connection,
    modrinth_rate_limiter: AsyncLimiter,
) -> Modrinth:
    return Modrinth(aiohttp_session, db_conn, modrinth_rate_limiter)

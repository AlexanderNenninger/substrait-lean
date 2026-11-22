"""Windows paths, read on any platform (#183): a table's default name and the
local path of a `file:` URI. The Windows trial found both (#2263)."""

from __future__ import annotations

import os
from pathlib import PureWindowsPath

import pytest

from sverify._scan import file_uri_path, local_path
from sverify.io.delta import _basename


@pytest.mark.parametrize(
    ("uri", "name"),
    [
        (r"C:\Users\me\lake\orders", "orders"),
        (r"C:\Users\me\lake\orders" + "\\", "orders"),
        ("C:/Users/me/lake/orders.v2", "orders_v2"),
        (r"\\server\share\lake\orders", "orders"),
        ("/home/me/lake/orders/", "orders"),
        ("s3://bucket/lake/orders", "orders"),
        ("uc://main.sales.orders", "orders"),
    ],
)
def test_a_table_is_named_after_the_last_part_of_its_path(uri, name):
    assert _basename(uri) == name


@pytest.mark.parametrize(
    ("uri", "path"),
    [
        ("file:///tmp/db/t/data/a.parquet", "/tmp/db/t/data/a.parquet"),
        ("file://localhost/tmp/a.parquet", "/tmp/a.parquet"),
        ("file:///C:/Users/me/db/t/a.parquet", "C:/Users/me/db/t/a.parquet"),
        # An f-string of a Windows path: the drive and its backslashes are the
        # URI's host, which `urlparse` keeps apart from the path.
        (r"file://C:\Users\me\db/t/data/a.parquet", r"C:\Users\me\db/t/data/a.parquet"),
        ("file://C:/Users/me/a%20b.parquet", "C:/Users/me/a b.parquet"),
        ("file://server/share/t/a.parquet", "//server/share/t/a.parquet"),
    ],
)
def test_a_file_uri_keeps_its_drive_and_host(uri, path):
    assert file_uri_path(uri) == path


def test_a_windows_file_uri_names_the_file_under_its_drive():
    path = PureWindowsPath(file_uri_path(r"file://C:\Users\me\db/orders/data/a.parquet"))
    assert path.parts == ("C:\\", "Users", "me", "db", "orders", "data", "a.parquet")


@pytest.mark.skipif(os.name == "nt", reason="Windows reads another host as a UNC share")
def test_a_file_uri_on_another_host_is_no_local_path():
    """`file://otherhost/x` names a file on that host; `//otherhost/x` would
    read as `/otherhost/x` here, so it is no local path (the review of #2280)."""
    assert local_path("file://otherhost/share/x.parquet") is None
    assert local_path("file://localhost/tmp/x.parquet") == "/tmp/x.parquet"

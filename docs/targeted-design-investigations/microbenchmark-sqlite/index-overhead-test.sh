set -eux

src=Fresh10000.sqlite
[ -f "$src" ] || { python extendDb.py "$src" 10000; chmod a-w "$src"; }

touch db1.sqlite
cp "$src" db1.sqlite

vmtouch -e db1.sqlite

date; python pruneDb.py db1.sqlite "$(sqlite3 db1.sqlite 'SELECT ebSlot FROM EB ORDER BY ebSlot LIMIT 1 OFFSET 3001-1')"; date

vmtouch -e db1.sqlite

date; python extendDb.py db1.sqlite 10000; date

touch db1.sqlite
cp "$src" db1.sqlite

vmtouch -e db1.sqlite

date; python pruneDb.py db1.sqlite "$(sqlite3 db1.sqlite 'SELECT ebSlot FROM EB ORDER BY ebSlot LIMIT 1 OFFSET 3000-1')"; date

vmtouch -e db1.sqlite

date; python extendDb.py db1.sqlite 10000; date

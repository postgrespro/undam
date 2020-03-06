This is PostgreSQL extension implementing UNDO storage based on table-AM API.
The primary goal is to address write amplification problem.
Right now Postgres MVCC implementation is creating new version of the object for
each update and unused version are collected later by vacuum.
Hot update mechanism is used to avoid insertion of new versions in indexes
but it is applicable only when version is located at the same page as update record.
Also hot updates does't eliminate table bloating on frequent updates.

Undam storage performs in-place update and stores old versions in undo chains.
Also tuple is splitted in fixed size chunks linked in L1-list.
So TOAST is not needed.

Undam relation is stored in two forks: main fork is used only for tuples headers
(first tuple chunk).  Tail chunks as well as undo versions are stored in the extension fork.
Old versions are also linked in L1 UNDO list. This list is traversed by transaction
which snapshot precedes creation of the last version and by vacuum.

Unfortunately current table-AM was developed mostly for hot-update model and doesn't
allow to update individual indexes which keys are affected by update.
It certainly limits advantages of Undam storage.

Undam storage is using the same visibility checking mechanism as standard PostgreSQL
heap (based on tuple's XMIN/XMAX and snapshots).

Undam storage also requires vacuum which freeze old tuples and truncated unneeded undo chains.

Undam storage is using generic WAL messages to provide ACID transaction behavior.
As far as it never shift data on the page, generic WAL messages delta calculation mechanism
is quite efficient in this case.

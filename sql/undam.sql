create extension undam;

create table t(pk bigint primary key, payload bigint) using undam;
insert into t values (generate_series(1,100000), 0);
update t set payload=payload+1;
vacuum t;
select * from undam_rel_info('t'::regclass);
drop table t;


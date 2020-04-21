CREATE FUNCTION undam_tableam_handler(INTERNAL) RETURNS table_am_handler
AS 'MODULE_PATHNAME' LANGUAGE C STRICT;

CREATE FUNCTION undam_rel_info(IN oid, OUT nScannedTuples int, OUT nScannedVersions int, OUT nScannedChunks int)
AS 'MODULE_PATHNAME' LANGUAGE C STRICT;

CREATE ACCESS METHOD undam
TYPE TABLE
HANDLER undam_tableam_handler;

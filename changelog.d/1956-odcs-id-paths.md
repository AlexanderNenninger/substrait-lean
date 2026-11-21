### `odcs.read` reads id paths to properties without an id

An id path such as `schema/products_obj/properties/id` names a property with no
`id` of its own by its `name`, as ODCS's example `schema/relationships.odcs.yaml`
writes it, so both foreign keys of that example read as `sv.references`. A
relationship sverify leaves unread now says why: it is not a foreign key, it
names a column the contract does not define, or it is a composite key (#2223)
(#1956).

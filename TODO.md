# TODO

- Find out if IV blocks needs MSB = 1 to have length == 96, or left most byte based.
  - Then find out how the fuck we're supposed to deal with that without billions of type conversions.
	- `GHASH((IV || 0^(128-len(IV)) << 128) ^ len(IV))`
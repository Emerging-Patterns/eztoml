# Changelog

## [0.3.0](https://github.com/Emerging-Patterns/eztoml/compare/v0.2.2...v0.3.0) (2026-09-24)


### Features

* add wf, the shapes parse returns ([d845ef7](https://github.com/Emerging-Patterns/eztoml/commit/d845ef75ee38a3b62acff1a8bda0fc1ce879ec83))
* land SPEC.md and retire the closed laws ([a5c6764](https://github.com/Emerging-Patterns/eztoml/commit/a5c676400edd6deedc3cff1476b117fcc9a503eb))
* **laws:** define same and own, with sanity laws for same ([14f62b3](https://github.com/Emerging-Patterns/eztoml/commit/14f62b3e5b6977bb63ce3eb27c0a2c9c99e286ad))
* **laws:** prove the key class, get and the readers, and part of at ([644d502](https://github.com/Emerging-Patterns/eztoml/commit/644d502fa565eb21639030ddd5f9d7778aa0973a))
* **laws:** prove TOML-GET-2, counting an array-of-tables element as a table ([8bb497c](https://github.com/Emerging-Patterns/eztoml/commit/8bb497c3bd8a56735499b376ececa76463bf22a7))
* **laws:** prove TOML-STR-2, how render writes a string ([befff47](https://github.com/Emerging-Patterns/eztoml/commit/befff4737e9a3f8fdfc6b9afe558b9e88e7c2758))
* move the interface to main.bend at the repository root ([234f606](https://github.com/Emerging-Patterns/eztoml/commit/234f606b859d13a3500b62618afb398f9c47784f))
* spec audit, SPEC.md, root layout, and the first proved rows and fixes ([ad78a59](https://github.com/Emerging-Patterns/eztoml/commit/ad78a596182b8827eb7b4ca0afaa2745479f92e0))


### Bug Fixes

* check a date's day against its month and leap years ([48470b1](https://github.com/Emerging-Patterns/eztoml/commit/48470b192341ff3f4486fb57acd08b8c11b131a3))
* read quotes before a multi-line closing delimiter and an empty string at the end ([8b863c5](https://github.com/Emerging-Patterns/eztoml/commit/8b863c5b2cfb0bc5493124f1a54d64f384db9dcb))
* refuse a second sign and an underscore after a leading zero ([3ebfb7f](https://github.com/Emerging-Patterns/eztoml/commit/3ebfb7fe8eaa67541311e1edf544d3112e0235ee))
* refuse controls in comments, a lone carriage return, and a value on the next line ([dd654d6](https://github.com/Emerging-Patterns/eztoml/commit/dd654d61c7ff36b4e8cc56fef5fe7b4244507e3c))

## [0.2.2](https://github.com/Emerging-Patterns/eztoml/compare/v0.2.1...v0.2.2) (2026-09-22)


### Performance Improvements

* quote plain string spans without the escape walk ([#22](https://github.com/Emerging-Patterns/eztoml/issues/22)) ([0b1bf3e](https://github.com/Emerging-Patterns/eztoml/commit/0b1bf3e8f4cb2b8e8b178a884c45c41261ac269a))

## [0.2.1](https://github.com/Emerging-Patterns/eztoml/compare/v0.2.0...v0.2.1) (2026-09-22)


### Performance Improvements

* cons table rows instead of appending on each key ([#20](https://github.com/Emerging-Patterns/eztoml/issues/20)) ([19fc461](https://github.com/Emerging-Patterns/eztoml/commit/19fc461ce8a8508b939308377291f90ff8ebf41a))

## [0.2.0](https://github.com/Emerging-Patterns/eztoml/compare/v0.1.0...v0.2.0) (2026-09-22)


### Features

* add fair Rust toml vs eztoml wave bench ([#18](https://github.com/Emerging-Patterns/eztoml/issues/18)) ([4ee64d8](https://github.com/Emerging-Patterns/eztoml/commit/4ee64d8e6dbba0e914f9469d91690dafdab524e2))

# Changelog

## [0.6.0](https://github.com/Emerging-Patterns/eztoml/compare/v0.5.0...v0.6.0) (2026-09-26)


### Features

* **laws:** TOML-KEY-3, keys in any spelling read back from every key position ([#52](https://github.com/Emerging-Patterns/eztoml/issues/52)) ([630fe66](https://github.com/Emerging-Patterns/eztoml/commit/630fe661341a23ccae1156e3f3a730cd08afcfc1))
* **laws:** WP-A chunk 1, an error stays, and headers and comments read as replay ([#67](https://github.com/Emerging-Patterns/eztoml/issues/67)) ([bbd3366](https://github.com/Emerging-Patterns/eztoml/commit/bbd3366c86ec3f2be0039a83692d8c17bb96fdeb))
* **laws:** WP-A, every short derivation parses to its replay ([#68](https://github.com/Emerging-Patterns/eztoml/issues/68)) ([65237e0](https://github.com/Emerging-Patterns/eztoml/commit/65237e0008ec2357a49a70ddac56f085de6e7523))
* **laws:** WP-G, toml.abnf transcribed as the grammar relation ([#60](https://github.com/Emerging-Patterns/eztoml/issues/60)) ([152cb83](https://github.com/Emerging-Patterns/eztoml/commit/152cb839ef260db1226a1c1e288b41647abd1d9c))
* **laws:** WP-N1, integer, float and boolean words exact in both directions ([#64](https://github.com/Emerging-Patterns/eztoml/issues/64)) ([5de5b3c](https://github.com/Emerging-Patterns/eztoml/commit/5de5b3cef61b64855caa33be842e123d900c369d))
* **laws:** WP-S1, strings of every form read as the text they denote; TOML-STR-1 proved ([#63](https://github.com/Emerging-Patterns/eztoml/issues/63)) ([8e28146](https://github.com/Emerging-Patterns/eztoml/commit/8e2814692ea31bd2ca395bc71655eef403c7d479))
* **laws:** WP-T1, datetime words exact in both directions ([#61](https://github.com/Emerging-Patterns/eztoml/issues/61)) ([f28b8d5](https://github.com/Emerging-Patterns/eztoml/commit/f28b8d590c96d7a5bfc2c93041c5e9c3c20e5c31))
* **laws:** WP-V, bare words read over parse; TOML-NUM-1, NUM-2 and TIME-1 proved ([#66](https://github.com/Emerging-Patterns/eztoml/issues/66)) ([a5cb83e](https://github.com/Emerging-Patterns/eztoml/commit/a5cb83e6c0d0e8619ac273ea78914057e31b9056))
* **proof:** an induction over parse for any invariant of the scanner's state ([#55](https://github.com/Emerging-Patterns/eztoml/issues/55)) ([d981c82](https://github.com/Emerging-Patterns/eztoml/commit/d981c82bf52d5afb79531541ca0c575a07440527))
* **proof:** TOML-KEY-3 proved, a key is found where it is put ([#56](https://github.com/Emerging-Patterns/eztoml/issues/56)) ([65756da](https://github.com/Emerging-Patterns/eztoml/commit/65756da4fdd955085f634c65b2e6b83ed2c5cc54))
* **proof:** WP-R spike, TEXT-1's refusal direction over the header and key states ([#62](https://github.com/Emerging-Patterns/eztoml/issues/62)) ([b129c22](https://github.com/Emerging-Patterns/eztoml/commit/b129c22404b6092707bf194bf767bcde0db0ade8))


### Bug Fixes

* a tab between a date and a time no longer reads as a datetime ([#65](https://github.com/Emerging-Patterns/eztoml/issues/65)) ([d0eda6a](https://github.com/Emerging-Patterns/eztoml/commit/d0eda6adf201790c0cfce3d09ceb7ffd9f221b88))

## [0.5.0](https://github.com/Emerging-Patterns/eztoml/compare/v0.4.0...v0.5.0) (2026-09-25)


### Features

* **laws:** WP-R2, parse then render is stable (TOML-RT-2 proved) ([#49](https://github.com/Emerging-Patterns/eztoml/issues/49)) ([6e3a716](https://github.com/Emerging-Patterns/eztoml/commit/6e3a7164b76510c56764ab4d87df72bc32d8bc7c))
* **laws:** WP-R3 spike, TOML-RT-3's invariant over every scanner state ([#42](https://github.com/Emerging-Patterns/eztoml/issues/42)) ([af800c1](https://github.com/Emerging-Patterns/eztoml/commit/af800c1a81b87c3ab993bf29792217ab5ff76d47))
* **laws:** WP-R3, parse gives a well-formed document (TOML-RT-3 proved) ([#47](https://github.com/Emerging-Patterns/eztoml/issues/47)) ([ba9c31e](https://github.com/Emerging-Patterns/eztoml/commit/ba9c31e28c8153d8180951225d7cc3efde0b1df8))


### Bug Fixes

* bend 2.0.28, no numeric name segments ([#48](https://github.com/Emerging-Patterns/eztoml/issues/48)) ([7a0fe8d](https://github.com/Emerging-Patterns/eztoml/commit/7a0fe8dc4f2d3cd47f0a59f9b0e2cdf2a5b0a3fd))

## [0.4.0](https://github.com/Emerging-Patterns/eztoml/compare/v0.3.1...v0.4.0) (2026-09-25)


### Features

* **laws:** a header of bare segments joined by dots reads back ([288e469](https://github.com/Emerging-Patterns/eztoml/commit/288e469b5e1e50023c046af2d0697c72fcc617a5))
* **laws:** a header of one bare segment reads back ([d672189](https://github.com/Emerging-Patterns/eztoml/commit/d67218981b50b9bd7c4ab0bbbcc6db07d37853a6))
* **laws:** a table set by the walk reads back as what it was set to ([abbf69b](https://github.com/Emerging-Patterns/eztoml/commit/abbf69b455e85d37ed3c6e07e57d7ef196da4ac2))
* **laws:** allow blank space in the headers the spelled-segment laws read ([4f2b7a1](https://github.com/Emerging-Patterns/eztoml/commit/4f2b7a1a3d2754a35a8fa0c323f63fa59611ad61))
* **laws:** array-of-tables headers read back ([5abadbb](https://github.com/Emerging-Patterns/eztoml/commit/5abadbbf25f8e51c786c6e43f856077a3a43791b))
* **laws:** contracts of the table walk (WP-W) ([e2494f4](https://github.com/Emerging-Patterns/eztoml/commit/e2494f48d4f7b02fe6b168b28d0e2ad753583d8f))
* **laws:** contracts of the walk for a put and a table header ([dced53b](https://github.com/Emerging-Patterns/eztoml/commit/dced53ba5ca0891aa71b823683dd0f69521b355b))
* **laws:** contracts of the walk for an array-of-tables header and a failed walk ([86fc6e3](https://github.com/Emerging-Patterns/eztoml/commit/86fc6e3c275d4191feb6bc66e5fbf6507c71a708))
* **laws:** header segments read back under their names, quoted or bare ([90a64c5](https://github.com/Emerging-Patterns/eztoml/commit/90a64c5ffd685bd045b400061029b154028327bb))
* **laws:** literal keys, dotted keys and spelled header segments read back (WP-K3) ([4fb7944](https://github.com/Emerging-Patterns/eztoml/commit/4fb7944ea8c3e499c5e2c4c2075233bcf4d552f3))
* **laws:** numbers, booleans and datetimes read back (WP-N) ([ca81791](https://github.com/Emerging-Patterns/eztoml/commit/ca81791dfe35efd5314f62fb5c42bc7152ffa7fb))
* **laws:** prove TOML-KEY-2, and plan the round-trip proofs ([b00055e](https://github.com/Emerging-Patterns/eztoml/commit/b00055ece9dc566fa547aa1de516bd0c323890b4))
* **laws:** prove TOML-KEY-2's read-back ([5a24d72](https://github.com/Emerging-Patterns/eztoml/commit/5a24d729c93398333b7ac6fa996a787ad841bfec))
* **laws:** prove TOML-RT-1 for a document of one string pair ([acda4c5](https://github.com/Emerging-Patterns/eztoml/commit/acda4c532661243cf9300c6f8e87589a9f815f8a))
* **laws:** put a dotted key's value under its segments' tables and find it with at ([a6c136f](https://github.com/Emerging-Patterns/eztoml/commit/a6c136feab151585455031a0cd2a01aa6a69c6ca))
* **laws:** read a bare value back from any value state, and booleans ([e310d11](https://github.com/Emerging-Patterns/eztoml/commit/e310d11ee49c190272a6a5445c0aa2a33083dad4))
* **laws:** read a document of one pair of any value back as itself ([047e874](https://github.com/Emerging-Patterns/eztoml/commit/047e874fa9b272d202398e2659642da072f9b0b9))
* **laws:** read a dotted key back as its segments' names ([6858cb4](https://github.com/Emerging-Patterns/eztoml/commit/6858cb4609b4892a6a9c18b38504575f71d4a84d))
* **laws:** read a literal key back as its characters ([4b9541c](https://github.com/Emerging-Patterns/eztoml/commit/4b9541c2c4e1dd3ad71136a74d8c40e8f737f9cd))
* **laws:** read a scalar back up to a comma, a closer or a newline ([56e95cf](https://github.com/Emerging-Patterns/eztoml/commit/56e95cfbcb99820b09a364c43d37fa1e392b0297))
* **laws:** read a string's span back from any value position ([3e43886](https://github.com/Emerging-Patterns/eztoml/commit/3e438863da3423c8fa4e49aeac132b762ec5ce13))
* **laws:** read a well-formed datetime back, and every scalar from any value state ([ddf84f8](https://github.com/Emerging-Patterns/eztoml/commit/ddf84f801eecd78070f812977484f3a0b328c8d5))
* **laws:** read a well-formed float back as its sign and spelling ([318914b](https://github.com/Emerging-Patterns/eztoml/commit/318914b969726c35c5cb42f4a3df2c38889f82eb))
* **laws:** read a well-formed integer back as its sign and digits ([908a9a6](https://github.com/Emerging-Patterns/eztoml/commit/908a9a63a14dbc5af8a1c1026b13af7b16241c5c))
* **laws:** read an array's items back one at a time ([7960655](https://github.com/Emerging-Patterns/eztoml/commit/796065517ecdc4db711bd7a97a4123684d6d4cd7))
* **laws:** read an inline table's pairs back one at a time ([b50b9f9](https://github.com/Emerging-Patterns/eztoml/commit/b50b9f900b9dec19afd9674a412a5a9b6d5e3b96))
* **laws:** read any well-formed value back, nested to any depth ([67a5aa5](https://github.com/Emerging-Patterns/eztoml/commit/67a5aa5453b5b952a143155080c6e7a020d592a6))
* **laws:** read back a nonempty string with escapes from any value position ([9bf9a5b](https://github.com/Emerging-Patterns/eztoml/commit/9bf9a5b72c6dabdcfa55d639f9d6b91eddea743a))
* **laws:** read back every rendered string in each value position ([51d4f7e](https://github.com/Emerging-Patterns/eztoml/commit/51d4f7e0a7a17e71eae848444cfc1fadf33e6589))
* **laws:** read header segments back however they are spelled ([0d01349](https://github.com/Emerging-Patterns/eztoml/commit/0d01349348bc8ef3b2afe4ec4bf53580c5fd59b5))
* **laws:** rendered strings read back in every value position (WP-S) ([fd3df38](https://github.com/Emerging-Patterns/eztoml/commit/fd3df38d2be19d63dc3067b7a24d7e79901a3746))
* **laws:** rows.seal puts the newest row last ([74589d7](https://github.com/Emerging-Patterns/eztoml/commit/74589d79d2e6e3423e2c6293e4d51ba9520e44f7))
* **laws:** table headers read back (WP-H) ([f8b1078](https://github.com/Emerging-Patterns/eztoml/commit/f8b1078e6b72c916cc38de0e7b18a9a469e37a9f))
* **laws:** WP-C, arrays and inline tables read back ([56d3967](https://github.com/Emerging-Patterns/eztoml/commit/56d3967d0876c4d7971342e9a5f3937ac6971017))


### Performance Improvements

* **proofs:** compute each control's escape once ([de6c356](https://github.com/Emerging-Patterns/eztoml/commit/de6c356bba3017302bd7a1a8381b7d29b953eb86))
* **proofs:** compute each control's escape once ([2969a39](https://github.com/Emerging-Patterns/eztoml/commit/2969a394f69a39ead4f9e8d0c20824b1f8f1f443))

## [0.3.1](https://github.com/Emerging-Patterns/eztoml/compare/v0.3.0...v0.3.1) (2026-09-24)


### Bug Fixes

* table, dotted-key and header conformance (I1, R2, V2, R3, I8) ([35f8414](https://github.com/Emerging-Patterns/eztoml/commit/35f841424222c31f35eccb7ae6ec5582063ded97))

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

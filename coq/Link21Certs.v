(** * Link size 21 in the kernel, and the descent from 21

    The 407,115 link classes of size 21 ([classes_21.txt.gz]) each carry a
    branch-and-bound tree over the finer model of [Link23], checked by
    [classcheck_m], in 538 modules ([Link21s0] to [Link21s537]).  Each
    module exports its class list and proves every class [CheckedClass];
    the certificates stay inside that opaque proof.  With the classes of
    sizes 22–27 ([Link22Certs.classes22]) this gives the descent at 21 and
    [g(4) ≤ 76], conditional on [ι(4) ≤ 27] and on the census being
    complete from 21 up ([CensusL classes21 21]).  See docs/roadmap.md §72. *)

From Coq Require Import List Lia.
Import ListNotations.
From Sunflower Require Import Sunflower IotaRate LinkCombine LinkLP Link23 Link22Certs
  Link21s0 Link21s1 Link21s2 Link21s3 Link21s4 Link21s5 Link21s6 Link21s7 Link21s8 Link21s9 Link21s10 Link21s11 Link21s12 Link21s13 Link21s14 Link21s15 Link21s16 Link21s17 Link21s18 Link21s19 Link21s20 Link21s21 Link21s22 Link21s23 Link21s24 Link21s25 Link21s26 Link21s27 Link21s28 Link21s29 Link21s30 Link21s31 Link21s32 Link21s33 Link21s34 Link21s35 Link21s36 Link21s37 Link21s38 Link21s39 Link21s40 Link21s41 Link21s42 Link21s43 Link21s44 Link21s45 Link21s46 Link21s47 Link21s48 Link21s49 Link21s50 Link21s51 Link21s52 Link21s53 Link21s54 Link21s55 Link21s56 Link21s57 Link21s58 Link21s59 Link21s60 Link21s61 Link21s62 Link21s63 Link21s64 Link21s65 Link21s66 Link21s67 Link21s68 Link21s69 Link21s70 Link21s71 Link21s72 Link21s73 Link21s74 Link21s75 Link21s76 Link21s77 Link21s78 Link21s79 Link21s80 Link21s81 Link21s82 Link21s83 Link21s84 Link21s85 Link21s86 Link21s87 Link21s88 Link21s89 Link21s90 Link21s91 Link21s92 Link21s93 Link21s94 Link21s95 Link21s96 Link21s97 Link21s98 Link21s99 Link21s100 Link21s101 Link21s102 Link21s103 Link21s104 Link21s105 Link21s106 Link21s107 Link21s108 Link21s109 Link21s110 Link21s111 Link21s112 Link21s113 Link21s114 Link21s115 Link21s116 Link21s117 Link21s118 Link21s119 Link21s120 Link21s121 Link21s122 Link21s123 Link21s124 Link21s125 Link21s126 Link21s127 Link21s128 Link21s129 Link21s130 Link21s131 Link21s132 Link21s133 Link21s134 Link21s135 Link21s136 Link21s137 Link21s138 Link21s139 Link21s140 Link21s141 Link21s142 Link21s143 Link21s144 Link21s145 Link21s146 Link21s147 Link21s148 Link21s149 Link21s150 Link21s151 Link21s152 Link21s153 Link21s154 Link21s155 Link21s156 Link21s157 Link21s158 Link21s159 Link21s160 Link21s161 Link21s162 Link21s163 Link21s164 Link21s165 Link21s166 Link21s167 Link21s168 Link21s169 Link21s170 Link21s171 Link21s172 Link21s173 Link21s174 Link21s175 Link21s176 Link21s177 Link21s178 Link21s179 Link21s180 Link21s181 Link21s182 Link21s183 Link21s184 Link21s185 Link21s186 Link21s187 Link21s188 Link21s189 Link21s190 Link21s191 Link21s192 Link21s193 Link21s194 Link21s195 Link21s196 Link21s197 Link21s198 Link21s199 Link21s200 Link21s201 Link21s202 Link21s203 Link21s204 Link21s205 Link21s206 Link21s207 Link21s208 Link21s209 Link21s210 Link21s211 Link21s212 Link21s213 Link21s214 Link21s215 Link21s216 Link21s217 Link21s218 Link21s219 Link21s220 Link21s221 Link21s222 Link21s223 Link21s224 Link21s225 Link21s226 Link21s227 Link21s228 Link21s229 Link21s230 Link21s231 Link21s232 Link21s233 Link21s234 Link21s235 Link21s236 Link21s237 Link21s238 Link21s239 Link21s240 Link21s241 Link21s242 Link21s243 Link21s244 Link21s245 Link21s246 Link21s247 Link21s248 Link21s249 Link21s250 Link21s251 Link21s252 Link21s253 Link21s254 Link21s255 Link21s256 Link21s257 Link21s258 Link21s259 Link21s260 Link21s261 Link21s262 Link21s263 Link21s264 Link21s265 Link21s266 Link21s267 Link21s268 Link21s269 Link21s270 Link21s271 Link21s272 Link21s273 Link21s274 Link21s275 Link21s276 Link21s277 Link21s278 Link21s279 Link21s280 Link21s281 Link21s282 Link21s283 Link21s284 Link21s285 Link21s286 Link21s287 Link21s288 Link21s289 Link21s290 Link21s291 Link21s292 Link21s293 Link21s294 Link21s295 Link21s296 Link21s297 Link21s298 Link21s299 Link21s300 Link21s301 Link21s302 Link21s303 Link21s304 Link21s305 Link21s306 Link21s307 Link21s308 Link21s309 Link21s310 Link21s311 Link21s312 Link21s313 Link21s314 Link21s315 Link21s316 Link21s317 Link21s318 Link21s319 Link21s320 Link21s321 Link21s322 Link21s323 Link21s324 Link21s325 Link21s326 Link21s327 Link21s328 Link21s329 Link21s330 Link21s331 Link21s332 Link21s333 Link21s334 Link21s335 Link21s336 Link21s337 Link21s338 Link21s339 Link21s340 Link21s341 Link21s342 Link21s343 Link21s344 Link21s345 Link21s346 Link21s347 Link21s348 Link21s349 Link21s350 Link21s351 Link21s352 Link21s353 Link21s354 Link21s355 Link21s356 Link21s357 Link21s358 Link21s359 Link21s360 Link21s361 Link21s362 Link21s363 Link21s364 Link21s365 Link21s366 Link21s367 Link21s368 Link21s369 Link21s370 Link21s371 Link21s372 Link21s373 Link21s374 Link21s375 Link21s376 Link21s377 Link21s378 Link21s379 Link21s380 Link21s381 Link21s382 Link21s383 Link21s384 Link21s385 Link21s386 Link21s387 Link21s388 Link21s389 Link21s390 Link21s391 Link21s392 Link21s393 Link21s394 Link21s395 Link21s396 Link21s397 Link21s398 Link21s399 Link21s400 Link21s401 Link21s402 Link21s403 Link21s404 Link21s405 Link21s406 Link21s407 Link21s408 Link21s409 Link21s410 Link21s411 Link21s412 Link21s413 Link21s414 Link21s415 Link21s416 Link21s417 Link21s418 Link21s419 Link21s420 Link21s421 Link21s422 Link21s423 Link21s424 Link21s425 Link21s426 Link21s427 Link21s428 Link21s429 Link21s430 Link21s431 Link21s432 Link21s433 Link21s434 Link21s435 Link21s436 Link21s437 Link21s438 Link21s439 Link21s440 Link21s441 Link21s442 Link21s443 Link21s444 Link21s445 Link21s446 Link21s447 Link21s448 Link21s449 Link21s450 Link21s451 Link21s452 Link21s453 Link21s454 Link21s455 Link21s456 Link21s457 Link21s458 Link21s459 Link21s460 Link21s461 Link21s462 Link21s463 Link21s464 Link21s465 Link21s466 Link21s467 Link21s468 Link21s469 Link21s470 Link21s471 Link21s472 Link21s473 Link21s474 Link21s475 Link21s476 Link21s477 Link21s478 Link21s479 Link21s480 Link21s481 Link21s482 Link21s483 Link21s484 Link21s485 Link21s486 Link21s487 Link21s488 Link21s489 Link21s490 Link21s491 Link21s492 Link21s493 Link21s494 Link21s495 Link21s496 Link21s497 Link21s498 Link21s499 Link21s500 Link21s501 Link21s502 Link21s503 Link21s504 Link21s505 Link21s506 Link21s507 Link21s508 Link21s509 Link21s510 Link21s511 Link21s512 Link21s513 Link21s514 Link21s515 Link21s516 Link21s517 Link21s518 Link21s519 Link21s520 Link21s521 Link21s522 Link21s523 Link21s524 Link21s525 Link21s526 Link21s527 Link21s528 Link21s529 Link21s530 Link21s531 Link21s532 Link21s533 Link21s534 Link21s535 Link21s536 Link21s537.

(** Every certified link class of size 21 to 27. *)
Definition classes21 : list Family :=
  classes22 ++
  l21s0_classes ++
  l21s1_classes ++
  l21s2_classes ++
  l21s3_classes ++
  l21s4_classes ++
  l21s5_classes ++
  l21s6_classes ++
  l21s7_classes ++
  l21s8_classes ++
  l21s9_classes ++
  l21s10_classes ++
  l21s11_classes ++
  l21s12_classes ++
  l21s13_classes ++
  l21s14_classes ++
  l21s15_classes ++
  l21s16_classes ++
  l21s17_classes ++
  l21s18_classes ++
  l21s19_classes ++
  l21s20_classes ++
  l21s21_classes ++
  l21s22_classes ++
  l21s23_classes ++
  l21s24_classes ++
  l21s25_classes ++
  l21s26_classes ++
  l21s27_classes ++
  l21s28_classes ++
  l21s29_classes ++
  l21s30_classes ++
  l21s31_classes ++
  l21s32_classes ++
  l21s33_classes ++
  l21s34_classes ++
  l21s35_classes ++
  l21s36_classes ++
  l21s37_classes ++
  l21s38_classes ++
  l21s39_classes ++
  l21s40_classes ++
  l21s41_classes ++
  l21s42_classes ++
  l21s43_classes ++
  l21s44_classes ++
  l21s45_classes ++
  l21s46_classes ++
  l21s47_classes ++
  l21s48_classes ++
  l21s49_classes ++
  l21s50_classes ++
  l21s51_classes ++
  l21s52_classes ++
  l21s53_classes ++
  l21s54_classes ++
  l21s55_classes ++
  l21s56_classes ++
  l21s57_classes ++
  l21s58_classes ++
  l21s59_classes ++
  l21s60_classes ++
  l21s61_classes ++
  l21s62_classes ++
  l21s63_classes ++
  l21s64_classes ++
  l21s65_classes ++
  l21s66_classes ++
  l21s67_classes ++
  l21s68_classes ++
  l21s69_classes ++
  l21s70_classes ++
  l21s71_classes ++
  l21s72_classes ++
  l21s73_classes ++
  l21s74_classes ++
  l21s75_classes ++
  l21s76_classes ++
  l21s77_classes ++
  l21s78_classes ++
  l21s79_classes ++
  l21s80_classes ++
  l21s81_classes ++
  l21s82_classes ++
  l21s83_classes ++
  l21s84_classes ++
  l21s85_classes ++
  l21s86_classes ++
  l21s87_classes ++
  l21s88_classes ++
  l21s89_classes ++
  l21s90_classes ++
  l21s91_classes ++
  l21s92_classes ++
  l21s93_classes ++
  l21s94_classes ++
  l21s95_classes ++
  l21s96_classes ++
  l21s97_classes ++
  l21s98_classes ++
  l21s99_classes ++
  l21s100_classes ++
  l21s101_classes ++
  l21s102_classes ++
  l21s103_classes ++
  l21s104_classes ++
  l21s105_classes ++
  l21s106_classes ++
  l21s107_classes ++
  l21s108_classes ++
  l21s109_classes ++
  l21s110_classes ++
  l21s111_classes ++
  l21s112_classes ++
  l21s113_classes ++
  l21s114_classes ++
  l21s115_classes ++
  l21s116_classes ++
  l21s117_classes ++
  l21s118_classes ++
  l21s119_classes ++
  l21s120_classes ++
  l21s121_classes ++
  l21s122_classes ++
  l21s123_classes ++
  l21s124_classes ++
  l21s125_classes ++
  l21s126_classes ++
  l21s127_classes ++
  l21s128_classes ++
  l21s129_classes ++
  l21s130_classes ++
  l21s131_classes ++
  l21s132_classes ++
  l21s133_classes ++
  l21s134_classes ++
  l21s135_classes ++
  l21s136_classes ++
  l21s137_classes ++
  l21s138_classes ++
  l21s139_classes ++
  l21s140_classes ++
  l21s141_classes ++
  l21s142_classes ++
  l21s143_classes ++
  l21s144_classes ++
  l21s145_classes ++
  l21s146_classes ++
  l21s147_classes ++
  l21s148_classes ++
  l21s149_classes ++
  l21s150_classes ++
  l21s151_classes ++
  l21s152_classes ++
  l21s153_classes ++
  l21s154_classes ++
  l21s155_classes ++
  l21s156_classes ++
  l21s157_classes ++
  l21s158_classes ++
  l21s159_classes ++
  l21s160_classes ++
  l21s161_classes ++
  l21s162_classes ++
  l21s163_classes ++
  l21s164_classes ++
  l21s165_classes ++
  l21s166_classes ++
  l21s167_classes ++
  l21s168_classes ++
  l21s169_classes ++
  l21s170_classes ++
  l21s171_classes ++
  l21s172_classes ++
  l21s173_classes ++
  l21s174_classes ++
  l21s175_classes ++
  l21s176_classes ++
  l21s177_classes ++
  l21s178_classes ++
  l21s179_classes ++
  l21s180_classes ++
  l21s181_classes ++
  l21s182_classes ++
  l21s183_classes ++
  l21s184_classes ++
  l21s185_classes ++
  l21s186_classes ++
  l21s187_classes ++
  l21s188_classes ++
  l21s189_classes ++
  l21s190_classes ++
  l21s191_classes ++
  l21s192_classes ++
  l21s193_classes ++
  l21s194_classes ++
  l21s195_classes ++
  l21s196_classes ++
  l21s197_classes ++
  l21s198_classes ++
  l21s199_classes ++
  l21s200_classes ++
  l21s201_classes ++
  l21s202_classes ++
  l21s203_classes ++
  l21s204_classes ++
  l21s205_classes ++
  l21s206_classes ++
  l21s207_classes ++
  l21s208_classes ++
  l21s209_classes ++
  l21s210_classes ++
  l21s211_classes ++
  l21s212_classes ++
  l21s213_classes ++
  l21s214_classes ++
  l21s215_classes ++
  l21s216_classes ++
  l21s217_classes ++
  l21s218_classes ++
  l21s219_classes ++
  l21s220_classes ++
  l21s221_classes ++
  l21s222_classes ++
  l21s223_classes ++
  l21s224_classes ++
  l21s225_classes ++
  l21s226_classes ++
  l21s227_classes ++
  l21s228_classes ++
  l21s229_classes ++
  l21s230_classes ++
  l21s231_classes ++
  l21s232_classes ++
  l21s233_classes ++
  l21s234_classes ++
  l21s235_classes ++
  l21s236_classes ++
  l21s237_classes ++
  l21s238_classes ++
  l21s239_classes ++
  l21s240_classes ++
  l21s241_classes ++
  l21s242_classes ++
  l21s243_classes ++
  l21s244_classes ++
  l21s245_classes ++
  l21s246_classes ++
  l21s247_classes ++
  l21s248_classes ++
  l21s249_classes ++
  l21s250_classes ++
  l21s251_classes ++
  l21s252_classes ++
  l21s253_classes ++
  l21s254_classes ++
  l21s255_classes ++
  l21s256_classes ++
  l21s257_classes ++
  l21s258_classes ++
  l21s259_classes ++
  l21s260_classes ++
  l21s261_classes ++
  l21s262_classes ++
  l21s263_classes ++
  l21s264_classes ++
  l21s265_classes ++
  l21s266_classes ++
  l21s267_classes ++
  l21s268_classes ++
  l21s269_classes ++
  l21s270_classes ++
  l21s271_classes ++
  l21s272_classes ++
  l21s273_classes ++
  l21s274_classes ++
  l21s275_classes ++
  l21s276_classes ++
  l21s277_classes ++
  l21s278_classes ++
  l21s279_classes ++
  l21s280_classes ++
  l21s281_classes ++
  l21s282_classes ++
  l21s283_classes ++
  l21s284_classes ++
  l21s285_classes ++
  l21s286_classes ++
  l21s287_classes ++
  l21s288_classes ++
  l21s289_classes ++
  l21s290_classes ++
  l21s291_classes ++
  l21s292_classes ++
  l21s293_classes ++
  l21s294_classes ++
  l21s295_classes ++
  l21s296_classes ++
  l21s297_classes ++
  l21s298_classes ++
  l21s299_classes ++
  l21s300_classes ++
  l21s301_classes ++
  l21s302_classes ++
  l21s303_classes ++
  l21s304_classes ++
  l21s305_classes ++
  l21s306_classes ++
  l21s307_classes ++
  l21s308_classes ++
  l21s309_classes ++
  l21s310_classes ++
  l21s311_classes ++
  l21s312_classes ++
  l21s313_classes ++
  l21s314_classes ++
  l21s315_classes ++
  l21s316_classes ++
  l21s317_classes ++
  l21s318_classes ++
  l21s319_classes ++
  l21s320_classes ++
  l21s321_classes ++
  l21s322_classes ++
  l21s323_classes ++
  l21s324_classes ++
  l21s325_classes ++
  l21s326_classes ++
  l21s327_classes ++
  l21s328_classes ++
  l21s329_classes ++
  l21s330_classes ++
  l21s331_classes ++
  l21s332_classes ++
  l21s333_classes ++
  l21s334_classes ++
  l21s335_classes ++
  l21s336_classes ++
  l21s337_classes ++
  l21s338_classes ++
  l21s339_classes ++
  l21s340_classes ++
  l21s341_classes ++
  l21s342_classes ++
  l21s343_classes ++
  l21s344_classes ++
  l21s345_classes ++
  l21s346_classes ++
  l21s347_classes ++
  l21s348_classes ++
  l21s349_classes ++
  l21s350_classes ++
  l21s351_classes ++
  l21s352_classes ++
  l21s353_classes ++
  l21s354_classes ++
  l21s355_classes ++
  l21s356_classes ++
  l21s357_classes ++
  l21s358_classes ++
  l21s359_classes ++
  l21s360_classes ++
  l21s361_classes ++
  l21s362_classes ++
  l21s363_classes ++
  l21s364_classes ++
  l21s365_classes ++
  l21s366_classes ++
  l21s367_classes ++
  l21s368_classes ++
  l21s369_classes ++
  l21s370_classes ++
  l21s371_classes ++
  l21s372_classes ++
  l21s373_classes ++
  l21s374_classes ++
  l21s375_classes ++
  l21s376_classes ++
  l21s377_classes ++
  l21s378_classes ++
  l21s379_classes ++
  l21s380_classes ++
  l21s381_classes ++
  l21s382_classes ++
  l21s383_classes ++
  l21s384_classes ++
  l21s385_classes ++
  l21s386_classes ++
  l21s387_classes ++
  l21s388_classes ++
  l21s389_classes ++
  l21s390_classes ++
  l21s391_classes ++
  l21s392_classes ++
  l21s393_classes ++
  l21s394_classes ++
  l21s395_classes ++
  l21s396_classes ++
  l21s397_classes ++
  l21s398_classes ++
  l21s399_classes ++
  l21s400_classes ++
  l21s401_classes ++
  l21s402_classes ++
  l21s403_classes ++
  l21s404_classes ++
  l21s405_classes ++
  l21s406_classes ++
  l21s407_classes ++
  l21s408_classes ++
  l21s409_classes ++
  l21s410_classes ++
  l21s411_classes ++
  l21s412_classes ++
  l21s413_classes ++
  l21s414_classes ++
  l21s415_classes ++
  l21s416_classes ++
  l21s417_classes ++
  l21s418_classes ++
  l21s419_classes ++
  l21s420_classes ++
  l21s421_classes ++
  l21s422_classes ++
  l21s423_classes ++
  l21s424_classes ++
  l21s425_classes ++
  l21s426_classes ++
  l21s427_classes ++
  l21s428_classes ++
  l21s429_classes ++
  l21s430_classes ++
  l21s431_classes ++
  l21s432_classes ++
  l21s433_classes ++
  l21s434_classes ++
  l21s435_classes ++
  l21s436_classes ++
  l21s437_classes ++
  l21s438_classes ++
  l21s439_classes ++
  l21s440_classes ++
  l21s441_classes ++
  l21s442_classes ++
  l21s443_classes ++
  l21s444_classes ++
  l21s445_classes ++
  l21s446_classes ++
  l21s447_classes ++
  l21s448_classes ++
  l21s449_classes ++
  l21s450_classes ++
  l21s451_classes ++
  l21s452_classes ++
  l21s453_classes ++
  l21s454_classes ++
  l21s455_classes ++
  l21s456_classes ++
  l21s457_classes ++
  l21s458_classes ++
  l21s459_classes ++
  l21s460_classes ++
  l21s461_classes ++
  l21s462_classes ++
  l21s463_classes ++
  l21s464_classes ++
  l21s465_classes ++
  l21s466_classes ++
  l21s467_classes ++
  l21s468_classes ++
  l21s469_classes ++
  l21s470_classes ++
  l21s471_classes ++
  l21s472_classes ++
  l21s473_classes ++
  l21s474_classes ++
  l21s475_classes ++
  l21s476_classes ++
  l21s477_classes ++
  l21s478_classes ++
  l21s479_classes ++
  l21s480_classes ++
  l21s481_classes ++
  l21s482_classes ++
  l21s483_classes ++
  l21s484_classes ++
  l21s485_classes ++
  l21s486_classes ++
  l21s487_classes ++
  l21s488_classes ++
  l21s489_classes ++
  l21s490_classes ++
  l21s491_classes ++
  l21s492_classes ++
  l21s493_classes ++
  l21s494_classes ++
  l21s495_classes ++
  l21s496_classes ++
  l21s497_classes ++
  l21s498_classes ++
  l21s499_classes ++
  l21s500_classes ++
  l21s501_classes ++
  l21s502_classes ++
  l21s503_classes ++
  l21s504_classes ++
  l21s505_classes ++
  l21s506_classes ++
  l21s507_classes ++
  l21s508_classes ++
  l21s509_classes ++
  l21s510_classes ++
  l21s511_classes ++
  l21s512_classes ++
  l21s513_classes ++
  l21s514_classes ++
  l21s515_classes ++
  l21s516_classes ++
  l21s517_classes ++
  l21s518_classes ++
  l21s519_classes ++
  l21s520_classes ++
  l21s521_classes ++
  l21s522_classes ++
  l21s523_classes ++
  l21s524_classes ++
  l21s525_classes ++
  l21s526_classes ++
  l21s527_classes ++
  l21s528_classes ++
  l21s529_classes ++
  l21s530_classes ++
  l21s531_classes ++
  l21s532_classes ++
  l21s533_classes ++
  l21s534_classes ++
  l21s535_classes ++
  l21s536_classes ++
  l21s537_classes.

Lemma classes21_checked : forall D, In D classes21 -> CheckedAny D.
Proof.
  unfold classes21.
  apply checked_app; [exact classes22_checked |].
  apply checked_app; [exact (checked_hinted _ l21s0_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s1_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s2_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s3_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s4_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s5_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s6_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s7_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s8_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s9_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s10_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s11_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s12_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s13_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s14_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s15_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s16_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s17_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s18_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s19_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s20_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s21_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s22_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s23_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s24_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s25_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s26_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s27_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s28_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s29_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s30_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s31_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s32_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s33_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s34_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s35_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s36_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s37_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s38_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s39_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s40_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s41_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s42_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s43_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s44_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s45_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s46_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s47_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s48_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s49_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s50_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s51_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s52_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s53_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s54_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s55_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s56_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s57_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s58_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s59_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s60_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s61_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s62_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s63_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s64_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s65_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s66_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s67_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s68_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s69_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s70_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s71_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s72_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s73_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s74_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s75_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s76_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s77_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s78_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s79_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s80_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s81_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s82_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s83_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s84_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s85_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s86_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s87_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s88_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s89_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s90_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s91_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s92_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s93_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s94_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s95_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s96_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s97_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s98_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s99_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s100_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s101_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s102_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s103_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s104_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s105_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s106_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s107_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s108_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s109_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s110_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s111_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s112_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s113_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s114_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s115_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s116_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s117_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s118_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s119_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s120_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s121_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s122_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s123_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s124_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s125_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s126_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s127_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s128_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s129_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s130_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s131_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s132_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s133_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s134_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s135_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s136_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s137_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s138_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s139_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s140_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s141_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s142_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s143_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s144_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s145_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s146_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s147_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s148_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s149_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s150_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s151_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s152_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s153_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s154_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s155_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s156_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s157_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s158_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s159_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s160_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s161_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s162_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s163_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s164_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s165_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s166_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s167_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s168_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s169_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s170_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s171_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s172_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s173_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s174_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s175_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s176_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s177_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s178_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s179_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s180_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s181_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s182_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s183_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s184_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s185_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s186_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s187_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s188_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s189_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s190_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s191_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s192_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s193_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s194_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s195_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s196_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s197_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s198_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s199_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s200_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s201_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s202_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s203_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s204_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s205_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s206_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s207_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s208_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s209_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s210_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s211_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s212_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s213_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s214_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s215_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s216_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s217_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s218_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s219_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s220_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s221_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s222_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s223_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s224_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s225_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s226_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s227_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s228_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s229_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s230_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s231_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s232_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s233_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s234_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s235_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s236_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s237_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s238_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s239_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s240_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s241_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s242_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s243_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s244_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s245_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s246_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s247_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s248_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s249_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s250_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s251_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s252_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s253_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s254_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s255_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s256_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s257_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s258_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s259_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s260_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s261_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s262_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s263_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s264_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s265_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s266_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s267_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s268_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s269_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s270_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s271_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s272_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s273_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s274_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s275_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s276_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s277_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s278_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s279_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s280_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s281_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s282_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s283_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s284_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s285_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s286_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s287_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s288_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s289_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s290_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s291_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s292_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s293_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s294_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s295_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s296_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s297_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s298_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s299_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s300_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s301_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s302_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s303_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s304_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s305_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s306_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s307_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s308_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s309_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s310_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s311_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s312_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s313_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s314_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s315_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s316_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s317_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s318_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s319_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s320_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s321_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s322_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s323_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s324_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s325_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s326_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s327_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s328_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s329_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s330_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s331_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s332_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s333_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s334_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s335_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s336_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s337_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s338_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s339_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s340_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s341_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s342_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s343_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s344_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s345_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s346_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s347_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s348_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s349_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s350_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s351_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s352_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s353_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s354_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s355_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s356_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s357_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s358_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s359_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s360_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s361_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s362_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s363_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s364_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s365_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s366_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s367_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s368_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s369_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s370_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s371_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s372_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s373_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s374_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s375_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s376_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s377_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s378_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s379_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s380_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s381_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s382_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s383_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s384_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s385_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s386_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s387_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s388_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s389_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s390_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s391_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s392_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s393_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s394_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s395_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s396_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s397_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s398_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s399_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s400_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s401_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s402_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s403_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s404_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s405_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s406_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s407_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s408_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s409_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s410_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s411_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s412_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s413_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s414_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s415_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s416_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s417_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s418_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s419_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s420_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s421_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s422_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s423_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s424_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s425_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s426_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s427_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s428_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s429_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s430_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s431_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s432_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s433_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s434_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s435_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s436_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s437_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s438_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s439_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s440_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s441_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s442_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s443_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s444_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s445_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s446_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s447_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s448_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s449_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s450_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s451_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s452_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s453_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s454_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s455_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s456_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s457_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s458_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s459_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s460_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s461_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s462_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s463_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s464_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s465_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s466_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s467_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s468_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s469_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s470_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s471_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s472_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s473_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s474_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s475_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s476_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s477_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s478_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s479_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s480_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s481_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s482_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s483_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s484_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s485_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s486_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s487_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s488_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s489_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s490_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s491_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s492_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s493_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s494_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s495_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s496_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s497_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s498_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s499_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s500_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s501_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s502_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s503_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s504_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s505_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s506_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s507_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s508_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s509_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s510_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s511_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s512_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s513_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s514_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s515_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s516_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s517_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s518_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s519_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s520_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s521_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s522_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s523_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s524_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s525_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s526_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s527_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s528_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s529_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s530_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s531_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s532_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s533_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s534_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s535_ok) |].
  apply checked_app; [exact (checked_hinted _ l21s536_ok) |].
  exact (checked_hinted _ l21s537_ok).
Qed.

(** The descent at link size 21 and above. *)
Theorem descent_21 :
  IotaAtMost 4 27 -> CensusL classes21 21 -> LinkDescent 4 21 54.
Proof. intros Hi Hc; exact (descent_of_censusL Hi classes21 21 ltac:(lia) classes21_checked Hc). Qed.

Theorem g_four_at_most_76_of_census_21 :
  IotaAtMost 4 27 -> CensusL classes21 21 -> MeetingBound 4 56 -> GAtMost 4 76.
Proof.
  intros Hi Hc Hm.
  pose proof (g_at_most_of_descent_and_meeting 4 21 54 56 (descent_21 Hi Hc) Hm) as H.
  replace (Nat.max 54 (21 - 1 + 56)) with 76 in H by reflexivity. exact H.
Qed.

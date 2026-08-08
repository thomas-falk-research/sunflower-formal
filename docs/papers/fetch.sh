#!/bin/sh
# Rebuild the paper corpus from docs/papers/manifest.json and verify every
# byte against the SHA-256 recorded when it was read. Generated file: edit
# manifest.json and re-run tools/papers.py, not this script.
set -eu
cd "$(dirname "$0")"
RENDER=""
if [ "${1:-}" = "--render" ]; then RENDER=1; fi   # not && : set -e would exit
mkdir -p pdf
fail=0
get() { # key url file sha256
  if [ -f "pdf/$3" ]; then
    have=$(sha256sum "pdf/$3" | cut -d" " -f1)
    if [ "$have" = "$4" ]; then echo "ok       $1"; else echo "MISMATCH $1  (upstream changed; re-read before quoting)"; fail=1; fi
    return 0
  fi
  echo "fetch    $1  <- $2"
  if curl -sS -L --max-time 180 -A "sunflower-formal/1.0" -o "pdf/$3" "$2"; then
    have=$(sha256sum "pdf/$3" | cut -d" " -f1)
    if [ "$have" != "$4" ]; then echo "MISMATCH $1  expected $4 got $have"; fail=1; fi
  else echo "FAILED   $1"; fail=1; fi
}
get "ALWZ20" "https://arxiv.org/pdf/1908.08483v3" "alwz.pdf" "62dc8ba5bbda45653b2e73fcd9aa797dac027eaeb83aa687545b99884e27572f"
get "ASU12" "https://eccc.weizmann.ac.il/report/2011/067/download" "asu12.pdf" "fccf31d66f6c8ceb733e9d2cc947ad6d6a9d52d6080c133154fb553a1c9417df"
get "AhNo26" "https://arxiv.org/pdf/2606.30593v1" "naslund_improved.pdf" "ea346d254074ac8e1e377c5a82f685f210da7c33808a5cc49d48f090f8771761"
get "AlHo20" "https://arxiv.org/pdf/2010.05992v1" "near_sunflowers.pdf" "171dde4d7494ce1a54e260ad8dde54bc2d881f19a8bea393196f86108a21a95a"
get "BCCGNSU17" "https://arxiv.org/pdf/1605.06702v4" "blasiak_capset.pdf" "c93f9682aa339065fc2039914afa882707c88794327e952429f941cd80839220"
get "BCW21" "https://arxiv.org/pdf/2009.09327v2" "bcw21.pdf" "ac7a19f532ad76836aa68017cb708c36e1ec959f330225fc7e2cc3b592ba122e"
get "DE25" "https://arxiv.org/pdf/2511.17142v1" "dukeerdos.pdf" "a92a80c3e1e045d1723a2e69ea6959611c3d43e7907fbaccd2f4e2629d9128e9"
get "EKR61" "https://users.renyi.hu/~p_erdos/1961-07.pdf" "ekr61.pdf" "e53f1ec72accc8e55ec8da360588b224542a9133216d4b82a6918bbe309ac821"
get "ErRa60" "https://users.renyi.hu/~p_erdos/1960-04.pdf" "er60.pdf" "c5a8781eb19ec31b561be82087048ff3a3ecd5b1789c696e5e9e36fda1fa4f3b"
get "ErRa69" "https://users.renyi.hu/~p_erdos/1969-02.pdf" "er69_ii.pdf" "2f0bfd6815418a73e2053b2bb757d669500c0d0903b0a26d74b2a7445bf3802c"
get "FKNP21" "https://arxiv.org/pdf/1910.13433v2" "fknp.pdf" "68c25296e0b535b8500ae552f3e6de28d3c62aca1ecf138ca4a627e9007dc451"
get "FPPTZ24" "https://arxiv.org/pdf/2310.16701v2" "odd_sunflowers.pdf" "eb6623d7c6fe44fb4319c65381d920726b3af8305c0ae395a5af6a23f3c57f97"
get "FPS21" "https://arxiv.org/pdf/2103.10497v2" "fox_pach_suk.pdf" "0e8af82bae6723c15ee129629639041de694beff3081f265e10f4ce8f41215bf"
get "Fuk25" "https://arxiv.org/pdf/2510.19037v2" "sublog.pdf" "00bb96ee675de07cadb5596474cf9a39d27b6f6ee9519df3c6eda728a1f39a2c"
get "GMR12" "https://arxiv.org/pdf/1205.3534v1" "gmr_dnf.pdf" "34b0472d139bd607e3b51236feaa5dc3e4772654e890be9adafad554935277db"
get "Gal26" "https://arxiv.org/pdf/2606.13656v1" "galah.pdf" "b8c35cca28ebd040f6537047258335535573e91eef81062e4fb232e696909e68"
get "HLC25" "https://arxiv.org/pdf/2512.20055v1" "harmonic_lcm.pdf" "a67396fc444de344f4c549216828c9aeb4e85a66b243e231b836a897fac0f23e"
get "JMR25" "https://arxiv.org/pdf/2501.13850v2" "vcdim2025.pdf" "84eac35915967ece70d3c9a924ab11f417bf794fa0ab48563cafe6438c609b9a"
get "Ku23" "https://arxiv.org/pdf/2309.00097v3" "ku_partitions.pdf" "df10d20e3809ed96b923eef3ee75bbaf8ceecbe9abb9ab7bf144f757c70c325c"
get "KuZa22" "https://arxiv.org/pdf/2203.13379v3" "kuza_spreadapprox.pdf" "5afdc60485e36ab6267fb3cba3632ff24a7858a90e84788d51a9e80ffc218120"
get "Kup25" "https://arxiv.org/pdf/2508.20132v1" "kupavskii_survey.pdf" "49b65debb37fc76c1c7d3424b867b0433d420e842780068dcf842abba8f85636"
get "Lovett25" "https://www.ias.edu/sites/default/files/Shachar%20Lovett%20Lecture%20Notes%201.pdf" "lovett_pcmi.pdf" "c6ef7ed148a704a0d0e883574ede2c304f734f019aad84d055565886559ea08b"
get "MNSZ22" "https://arxiv.org/pdf/2209.11347v2" "mnsz.pdf" "71064ec1380bfb962f11fa9e00a7d17fc360055b432360b3572280b0e4ca671b"
get "Mis26" "https://arxiv.org/pdf/2606.02667v2" "mis26_shifted.pdf" "9a337994c314416d1cb3530d856108f689d6324f7c1ab65ef1ee45175de77d1e"
get "Moon26" "https://arxiv.org/pdf/2605.08676v2" "moonflowers.pdf" "3ed326d4c785eb9c3124d8317b5cdac3d67aec6a48fd2f4b2d45ae1866376849"
get "NaSa17" "https://arxiv.org/pdf/1606.09575v1" "naslund_sawin.pdf" "3ff6de6019afcb9583d8328ec31ee2c8af32e8a39890aef84a0eb5f8c61fed59"
get "Ra20" "https://arxiv.org/pdf/1909.04774v2" "rao_coding.pdf" "bdd752f400a90e144f1dc07ef1369cded75598536e94d0299ffb6b3715e2cac4"
get "Rao25" "https://arxiv.org/pdf/2509.14790v1" "story.pdf" "1e7bf1988f2b669f2e5cb589c11cbe0e6041f8af2362ef85a5a4d34048eb6f0d"
get "SC26" "https://arxiv.org/pdf/2602.04610v2" "structured_canon.pdf" "6072a7da1316c05b123b0ec1f8a9dfab13055d95e0501833d6d4908a5bb22ad0"
get "SFP25" "https://arxiv.org/pdf/2509.16355v1" "sfprocess.pdf" "517aa9aabda5f6907c95bbf0d8adac47411a061bb1101d0cb1f4fa987ad84e18"
get "SFS26" "https://arxiv.org/pdf/2605.12232v1" "sfsubspaces.pdf" "00343b9572b8381018162c2fb92c456843bd6cc8daa3d7ffc58f359c9dcddc0d"
get "Schrijver05" "https://ir.cwi.nl/pub/14098/14098B.pdf" "schrijver_terwilliger.pdf" "903d7fd4f61a25899ea6ab7ab8b013f4c7225fd00d529e471796e3081bd0d4c2"
get "Smooth21" "https://arxiv.org/pdf/2106.11882v2" "smoother_spread.pdf" "47245216582e72b4e2574dbe20a03a72a0de4450af0b08912cef753c39f56711"
get "Thi21" "https://www.isa-afp.org/browser_info/current/AFP/Sunflowers/document.pdf" "afp_sunflowers.pdf" "0efa86fe09274690724aeb19156c260d0e2325e44fcdcf97897477a7e661cac3"
get "VS25" "https://arxiv.org/pdf/2505.03671v2" "vecspaces.pdf" "891b6405125e885287d57f3771c918edff0a625314fb4d3bb5ef6ddfa77f880b"
get "FHHZ17" "https://arxiv.org/abs/1703.03896" "fhhz_degree_hm.pdf" "bc05a37a43d3a617fe8087029ec367c725f8639fc5f28fa43e0ed2c2ffe823f6"
if [ -n "$RENDER" ]; then
  for f in pdf/*.pdf; do d="render/$(basename "$f" .pdf)"; mkdir -p "$d"; pdftoppm -png -r 150 "$f" "$d/p"; done
  echo "rendered to render/"
fi
[ "$fail" = 0 ] && echo "all records verified" || { echo "SOME RECORDS FAILED"; exit 1; }

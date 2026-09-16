unset shellHook
PATH=${PATH:-}
nix_saved_PATH="$PATH"
XDG_DATA_DIRS=${XDG_DATA_DIRS:-}
nix_saved_XDG_DATA_DIRS="$XDG_DATA_DIRS"
AR='ar'
export AR
AR_FOR_TARGET='ar'
export AR_FOR_TARGET
AS='as'
export AS
AS_FOR_TARGET='as'
export AS_FOR_TARGET
BASH='/nix/store/i27rhb3nr65rkrwz36bchkwmav6ggsmn-bash-5.3p9/bin/bash'
CC='gcc'
export CC
CC_FOR_TARGET='clang'
export CC_FOR_TARGET
CMAKE_INCLUDE_PATH='/nix/store/785jidgnryzj566s25s3rb262d4g5znb-nodejs-24.14.1/include:/nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env/include:/nix/store/0rn2xh3zciwdr8sjg79ir79dbr6lnmfb-gnumake-4.4.1/include:/nix/store/rhp41khpds0m218gdp4lagkhb957mi42-poppler-utils-25.10.0-dev/include:/nix/store/3yl2s5r3yph88imzbgbdrh8pbs9rcjcs-zlib-1.3.2-dev/include:/nix/store/r7bp82svf04jqw3x7wnjlyr951jkf85k-freetype-2.14.2-dev/include:/nix/store/bh64ycxf96cc4v43m77nszmpvbs0pfv7-bzip2-1.0.8-dev/include:/nix/store/1x1msj33z37b65vlxbs51l7i4j92qn9h-brotli-1.2.0-dev/include:/nix/store/h176f4dhbcpj4lpf8sn28vdqp1mks5jk-libpng-apng-1.6.56-dev/include:/nix/store/gjg4aagfcn6r96c73rz4rwbclbdqqc6v-fontconfig-2.17.1-dev/include:/nix/store/b63lk3n7piwf7a790c4cy0zinqi184fs-libjpeg-turbo-3.1.4-dev/include:/nix/store/5q46i43k18sspv8wjpasmrgl5n8y7j1s-openjpeg-2.5.4-dev/include:/nix/store/8zhjvm4vixgvg089nn4wv7hhxlp7qg2c-cairo-1.18.4-dev/include:/nix/store/hywlq1sf1prbyrhqwf2sbamazp1hghk1-pixman-0.46.4/include:/nix/store/1kx6y7spy0q6372hqrvib7mw21gaq5bq-libxext-1.3.7-dev/include:/nix/store/mvyxqkpyj2mgymljzj9bqi9bmz7ca5fk-xorgproto-2025.1/include:/nix/store/hd6i8dzybk2jqwqh6frarw30w15yqq9b-libxau-1.0.12-dev/include:/nix/store/94m0129pm3jlbg4fj8py92j1vi870m9c-libxrender-0.9.12-dev/include:/nix/store/4303g76pqhl7r8a2xvci0b4bj47bfbjz-libx11-1.8.13-dev/include:/nix/store/x44m80ahg51pz32dr0j39yzsr7bn7d5v-libxcb-1.17.0-dev/include:/nix/store/kw0yjwbvw6arwgwaa3p8rz46qsgy4626-glib-2.86.3-dev/include:/nix/store/lg8kfrcxy4bcwnlwbfn6x3s48k4aawba-libffi-3.5.2-dev/include:/nix/store/ypj27q94ay0ybq9aa14gk0cxjv9d7z4m-gettext-1.0/include:/nix/store/5722rfnbamx35h5df4wlvlqrmvmaan7i-glibc-iconv-2.42/include:/nix/store/pbyr7jlx85a0vlx623jqjd18cnccb5vv-lcms2-2.18-dev/include:/nix/store/ankisnmp03gzp9m0z4bqy1i2ar23wb48-libtiff-4.7.1-dev/include:/nix/store/7xvb5060qcf36ncp47wz62rl3fsccv1g-curl-8.19.0-dev/include:/nix/store/dgdzsx6i729gcp1rrz85zbaacgl86gab-krb5-1.22.1-dev/include:/nix/store/iaf80mkaj9kfgy3h6hf1xqj7la8acr7y-nghttp2-1.68.1-dev/include:/nix/store/d2xhslm8a0b1lk0p4plmyip3i194znhy-nghttp3-1.15.0-dev/include:/nix/store/yp754aaxmfqdag95053yax1fdaa4s9ck-ngtcp2-1.22.0-dev/include:/nix/store/j3ypygy4pwwgkdrkxkhnhxqkwx4yw8zq-libidn2-2.3.8-dev/include:/nix/store/dy64cxaygvmjfznysgxk501yds8jij6s-openssl-3.6.1-dev/include:/nix/store/ylldnaarbvwkvpn5dasnjjyvvghh6k3r-libpsl-0.21.5-dev/include:/nix/store/5c04s19in4y2ij0zzkh4y9gqys8rwgc4-libssh2-1.11.1-dev/include:/nix/store/vbqakw4shfcbmdxs6kkp3jmp9k5br94y-zstd-1.5.7-dev/include:/nix/store/xafb1qxw69j6fg1s8ln2drppm2zjjfr5-nss-3.112.3-dev/include:/nix/store/3qfr4jp73jac5rnkx8xj58whv4yc80zy-nspr-4.38.2-dev/include:/nix/store/l7nryi3685lc6di1wbyfmb5q3v3xmfqz-ghostscript-with-X-10.06.0/include:/nix/store/hn59rqwq5j0z7l13yns903l6ibylwz1g-imagemagick-7.1.2-19-dev/include:/nix/store/vd0i6w0g7wgj621lpzc2dsld42fsvh6c-libxt-1.3.1-dev/include:/nix/store/sl65d0g3k4f6v5w7xclx334zzcj1w533-libsm-1.2.6-dev/include:/nix/store/07rdpwd0gxa48k7p7p9mk6h0s0p5zknc-libice-1.1.2-dev/include:/nix/store/vdz5z5d4qvsfqdafihrfwzi5r7wr24lk-libwebp-1.6.0/include:/nix/store/wgz6lg6jd6rq3n7gxgaj8i9qm6f5xlbf-fftw-double-3.3.10-dev/include:/nix/store/p8x5zv9s9qg3ld8b7jdm03hkpdqybjl9-jq-1.8.1-dev/include:/nix/store/9xkb4la9kpnsbrs3kw2cij3wjfbv6j6g-duckdb-1.5.2-dev/include:/nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12/include:/nix/store/xswd8j43wkqpadsgfl3cnf1hibvwncrw-lld-19.1.7-dev/include:/nix/store/x78aqw188hv2nmj8hbbl4q9knhns4qf2-xz-5.8.3-dev/include:/nix/store/i7arixgp0p933iicqzfza1dm9g2vgbzf-lz4-1.10.0-dev/include:/nix/store/sw1dgmpi3s1vkjfbdjwj4bliz626fvqp-compiler-rt-libc-19.1.7-dev/include'
export CMAKE_INCLUDE_PATH
CMAKE_LIBRARY_PATH='/nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env/lib:/nix/store/ixhlv41i2wpl84xgjcks061dz4yssbg3-zlib-1.3.2/lib:/nix/store/2amncb4zvr32gm5d2i8m6gz29c02cn61-bzip2-1.0.8/lib:/nix/store/7ff90dag7i173s49c5m614wny2lpps1l-brotli-1.2.0-lib/lib:/nix/store/gsn3vddway3289p6mzy5shd1paly8dp4-libpng-apng-1.6.56/lib:/nix/store/zr22ggqbv79yv4y4wv06r4grla9h59yx-freetype-2.14.2/lib:/nix/store/bg6ms0vw071g1fdbx2my6bbzsk62p6vd-fontconfig-2.17.1-lib/lib:/nix/store/lsln4vpc8spwmb96vjjmg4yd0krd2r7c-libjpeg-turbo-3.1.4/lib:/nix/store/nrq3pjzsjd4w9vcpgk4a2wfjlqz4xxzw-openjpeg-2.5.4/lib:/nix/store/hywlq1sf1prbyrhqwf2sbamazp1hghk1-pixman-0.46.4/lib:/nix/store/2krkc90x3ch0mgkk48fxlglq14nqapdr-libxau-1.0.12/lib:/nix/store/n1ykqk7ibmp4h5r4x5fng4cn9wjlgj9y-libxext-1.3.7/lib:/nix/store/5m91jqg1526jzsahrgmd37k4ml3nc5l4-libx11-1.8.13/lib:/nix/store/dwavjjnzjmp7901n2s61kw40qw8c5rfc-libxrender-0.9.12/lib:/nix/store/fc1g44pg3i10wfzh3gb4m54pfgclsn76-libxcb-1.17.0/lib:/nix/store/hyai3q7gvdfppw4ky7s2mvhxvfyp5bh7-libffi-3.5.2/lib:/nix/store/ypj27q94ay0ybq9aa14gk0cxjv9d7z4m-gettext-1.0/lib:/nix/store/zcmsivndca5wmam9nwnbjrm0zkgykwfz-glib-2.86.3/lib:/nix/store/hgvr4xvcqm4a06rq5scgcy6nlk5q89gd-cairo-1.18.4/lib:/nix/store/3j2yd136zgln9w2hsrvlmazyrhcnfri5-lcms2-2.18/lib:/nix/store/6w9m0a1v9kx40q341wq4y337s8csqhyn-libtiff-4.7.1/lib:/nix/store/8cr60j6q7rqmcy4k8l6l1cay9579kd6y-krb5-1.22.1-lib/lib:/nix/store/hms747x82q23p2g6r6kgzqf7li2ryk39-nghttp2-1.68.1-lib/lib:/nix/store/133x0z91pizyk8zr4l2ccgqlclpkp1lj-nghttp3-1.15.0/lib:/nix/store/g5sd94mk8w1a0wiipk81ri0prk136d32-ngtcp2-1.22.0/lib:/nix/store/sgswwrxkhdlfskklqp4gsbi2cskfg07c-libidn2-2.3.8/lib:/nix/store/wbyqkb1vpm41s4jb8pv0i9h4jv08xdrv-openssl-3.6.1/lib:/nix/store/79kr7fafcvvmch13cyczpckz40159pk5-libpsl-0.21.5/lib:/nix/store/9lzm6krq5ikzbqbmazbh5jmzwph99rz3-libssh2-1.11.1/lib:/nix/store/k0rqiflg1vkn1kj96br5pfxj40p3srz4-zstd-1.5.7/lib:/nix/store/pz6b64891m180yb4hadj1jjg3wm3ybng-curl-8.19.0/lib:/nix/store/amjf7cch3hb5r6l646mwjhrr9384ks4s-nspr-4.38.2/lib:/nix/store/0wnl2h5xgy1q7bgkqdbiyzxnrq3cmigi-nss-3.112.3/lib:/nix/store/92ipcswac970qz2iq0nn1yw1jj69xm69-poppler-utils-25.10.0/lib:/nix/store/l7nryi3685lc6di1wbyfmb5q3v3xmfqz-ghostscript-with-X-10.06.0/lib:/nix/store/qhw8zihdm481cvia6pd0kl2fmqk9mr2k-libice-1.1.2/lib:/nix/store/wnmwabsnj34j46c579y0ypc29xjfxjwf-libsm-1.2.6/lib:/nix/store/vqisl3q8b600dhrpj2a12bk4r5vzn3g4-libxt-1.3.1/lib:/nix/store/vdz5z5d4qvsfqdafihrfwzi5r7wr24lk-libwebp-1.6.0/lib:/nix/store/84crpkdlv33nx4kahqzkss83fvpp8x3q-fftw-double-3.3.10/lib:/nix/store/pjcg9z9zj4hqa7y8jjgsx06rc31q6r8s-imagemagick-7.1.2-19/lib:/nix/store/09bq2i0kb008ccg3qdbyxv81ggxxnn09-jq-1.8.1/lib:/nix/store/kqjjmmq70c07hpizbd2sprryrx6a7bs5-duckdb-1.5.2-lib/lib:/nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12/lib:/nix/store/477l7v6l11yw7vc1gzmv8ybjl8rs799z-lld-19.1.7-lib/lib:/nix/store/hmslvsxvs2ijb7iw5krdckai2im6vp2y-xz-5.8.3/lib:/nix/store/fy28r1ynjk65gnj898k9dabyvzz9mryc-lz4-1.10.0-lib/lib'
export CMAKE_LIBRARY_PATH
CONFIG_SHELL='/nix/store/i27rhb3nr65rkrwz36bchkwmav6ggsmn-bash-5.3p9/bin/bash'
export CONFIG_SHELL
CXX='g++'
export CXX
CXX_FOR_TARGET='clang++'
export CXX_FOR_TARGET
DETERMINISTIC_BUILD='1'
export DETERMINISTIC_BUILD
GETTEXTDATADIRS='/nix/store/ypj27q94ay0ybq9aa14gk0cxjv9d7z4m-gettext-1.0/share/gettext:/nix/store/zcmsivndca5wmam9nwnbjrm0zkgykwfz-glib-2.86.3/share/gettext'
export GETTEXTDATADIRS
HOSTTYPE='x86_64'
HOST_PATH='/nix/store/785jidgnryzj566s25s3rb262d4g5znb-nodejs-24.14.1/bin:/nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env/bin:/nix/store/cifzx7qr3mpcphz1bnlww4llshrvczyg-pandoc-cli-3.7.0.2/bin:/nix/store/0rn2xh3zciwdr8sjg79ir79dbr6lnmfb-gnumake-4.4.1/bin:/nix/store/04ys3zgcil28yj4afyk6p3dlrfv60s1h-time-1.10/bin:/nix/store/r7bp82svf04jqw3x7wnjlyr951jkf85k-freetype-2.14.2-dev/bin:/nix/store/zj6r42syyswkhrr174bzppj3n7xhq936-bzip2-1.0.8-bin/bin:/nix/store/mj1k1nsdqr0mp9wsnkg7blgh3xf5wssv-brotli-1.2.0/bin:/nix/store/h176f4dhbcpj4lpf8sn28vdqp1mks5jk-libpng-apng-1.6.56-dev/bin:/nix/store/v18drszzvspk1wlq06r68nxgpn2b4cvd-fontconfig-2.17.1-bin/bin:/nix/store/v70k3ch8rcw9b0la3axqb34dkyxqnx2s-libjpeg-turbo-3.1.4-bin/bin:/nix/store/nrq3pjzsjd4w9vcpgk4a2wfjlqz4xxzw-openjpeg-2.5.4/bin:/nix/store/8zhjvm4vixgvg089nn4wv7hhxlp7qg2c-cairo-1.18.4-dev/bin:/nix/store/kw0yjwbvw6arwgwaa3p8rz46qsgy4626-glib-2.86.3-dev/bin:/nix/store/ypj27q94ay0ybq9aa14gk0cxjv9d7z4m-gettext-1.0/bin:/nix/store/b9jcqjd8gnxr87p7wc91lmbyd90kzlc1-glib-2.86.3-bin/bin:/nix/store/xiq38z94b68c8dgj7nfx9xlh2984c2mp-lcms2-2.18-bin/bin:/nix/store/cbdy1d44cqa9j7x0ga72dqsk4p49ih70-libtiff-4.7.1-bin/bin:/nix/store/7xvb5060qcf36ncp47wz62rl3fsccv1g-curl-8.19.0-dev/bin:/nix/store/dgdzsx6i729gcp1rrz85zbaacgl86gab-krb5-1.22.1-dev/bin:/nix/store/qp2qzmh67rqy6i36sh3iqznk1akiw4q1-krb5-1.22.1/bin:/nix/store/yvxyaqh3bzj7nr64zlr1axyf76fgcszb-nghttp2-1.68.1/bin:/nix/store/a327a5lqzwakcs3yjgx4sa1931fph5gf-libidn2-2.3.8-bin/bin:/nix/store/2di90l89y2ygdy3rbws7dhg9nrvd3pnx-openssl-3.6.1-bin/bin:/nix/store/79kr7fafcvvmch13cyczpckz40159pk5-libpsl-0.21.5/bin:/nix/store/91jddg4g6788ilnk3kww8j8jhxhzk6d3-zstd-1.5.7-bin/bin:/nix/store/k0rqiflg1vkn1kj96br5pfxj40p3srz4-zstd-1.5.7/bin:/nix/store/sm2nq18jjqp4x0sxpl6lrvwl9rx6mvj2-curl-8.19.0-bin/bin:/nix/store/xafb1qxw69j6fg1s8ln2drppm2zjjfr5-nss-3.112.3-dev/bin:/nix/store/3qfr4jp73jac5rnkx8xj58whv4yc80zy-nspr-4.38.2-dev/bin:/nix/store/92ipcswac970qz2iq0nn1yw1jj69xm69-poppler-utils-25.10.0/bin:/nix/store/l7nryi3685lc6di1wbyfmb5q3v3xmfqz-ghostscript-with-X-10.06.0/bin:/nix/store/hn59rqwq5j0z7l13yns903l6ibylwz1g-imagemagick-7.1.2-19-dev/bin:/nix/store/vdz5z5d4qvsfqdafihrfwzi5r7wr24lk-libwebp-1.6.0/bin:/nix/store/wgz6lg6jd6rq3n7gxgaj8i9qm6f5xlbf-fftw-double-3.3.10-dev/bin:/nix/store/pjcg9z9zj4hqa7y8jjgsx06rc31q6r8s-imagemagick-7.1.2-19/bin:/nix/store/v5c3inhfq6xshmwg1c254vfbcy4jp3k9-jq-1.8.1-bin/bin:/nix/store/n4h91v3p9v5hfgcrmfashil26nsrsrhs-duckdb-1.5.2/bin:/nix/store/jx6bzribg9fa0mxbr8b602rq74k24dr7-python3.13-yamllint-1.37.1/bin:/nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12/bin:/nix/store/7xiiq153kv13wcqb6j5zffz2g778nssv-shellcheck-0.11.0-bin/bin:/nix/store/hn7cpgmj18mx8lj5wsnjgcy158cnfyz1-statix-0.5.8/bin:/nix/store/ivy6wb23x19x29qz49y98amkch1jbz84-elan-4.2.1/bin:/nix/store/xiy3ydpzw5bdqqd7ri8qbg3bn4r2qxg1-rustup-1.29.0/bin:/nix/store/biagcw4fwc90ala8pxbdb919khj39rzy-clang-wrapper-19.1.7/bin:/nix/store/vr4sjc5ajni6j76wqkvkx84q141270ak-binutils-wrapper-2.46/bin:/nix/store/hvihdgv65b31lrw3rdybjz1m8q314qyi-lld-19.1.7/bin:/nix/store/v2i1hgv567g3v91im5x4g5bff52143i0-cmake-4.1.2/bin:/nix/store/v7mjkia7ki79s5i24ldbzq1khalhgzk0-pkg-config-wrapper-0.29.2/bin:/nix/store/fszv4kq85ywrpq6dy2wydl1ggkbc6sjp-emscripten-5.0.6/bin:/nix/store/pxhpmfr4qwihzxqam9642a9r7jpvbblr-typescript-5.9.3/bin:/nix/store/246dw7jxjgznw9fql388hj43yyknlqmn-vscode-1.116.0/bin:/nix/store/9lhr1c3l9qzv8pzp3idmii1nwvxxjys3-gzip-1.14/bin:/nix/store/2nm5c858fh52s6mhcffm07s3biaxys44-xz-5.8.3-bin/bin:/nix/store/m7m89ms25namgzbhcx6nf42jgjx55lcx-lz4-1.10.0/bin:/nix/store/qpf8bnaad0j8g4ggl65hvfs8l5y1alwp-mermaid-cli-11.12.0/bin:/nix/store/nkai8ssk915yc9mvj0xi28zliwwsaacp-zpaq-7.15/bin:/nix/store/0l71d5r282xjml5zhd3knf4syinczqwh-R-4.5.3-wrapper/bin:/nix/store/jjxngswsb214vb58qx485jhmilf0kxxy-coreutils-9.10/bin:/nix/store/vhsirn9m1ifmnw5g1qczzhvqkx6lw1if-findutils-4.10.0/bin:/nix/store/hx084k7pgz4n0vgkvil9gbcnl8y6p1xf-diffutils-3.12/bin:/nix/store/af4a8i43kc2ss4rnmf0swkk2mprsw6xq-gnused-4.9/bin:/nix/store/wf7lr2hf43546jc5kwqh3dbxnpcnw1mn-gnugrep-3.12/bin:/nix/store/lakv43kv98sl6h0ba6wnyg513mcq61vl-gawk-5.4.0/bin:/nix/store/rnvb7bvp53v2dw7pcwh9xb89x5z4rjib-gnutar-1.35/bin:/nix/store/9lhr1c3l9qzv8pzp3idmii1nwvxxjys3-gzip-1.14/bin:/nix/store/zj6r42syyswkhrr174bzppj3n7xhq936-bzip2-1.0.8-bin/bin:/nix/store/yvrwcs1a45rj8142n0l2w9q9s6akamjr-gnumake-4.4.1/bin:/nix/store/i27rhb3nr65rkrwz36bchkwmav6ggsmn-bash-5.3p9/bin:/nix/store/zj7mxwji29zvj9vl70iip7gw4h6ljfam-patch-2.8/bin:/nix/store/2nm5c858fh52s6mhcffm07s3biaxys44-xz-5.8.3-bin/bin:/nix/store/iscmg3ivhx7z67dz14lrg7p77gnsa4dw-file-5.45/bin'
export HOST_PATH
IFS=' 	
'
IN_NIX_SHELL='impure'
export IN_NIX_SHELL
LD='ld'
export LD
LD_FOR_TARGET='ld'
export LD_FOR_TARGET
LINENO='76'
MACHTYPE='x86_64-pc-linux-gnu'
NIXPKGS_CMAKE_PREFIX_PATH='/nix/store/66lksljlljdd5ppgvfk8g89y8xgqcxd7-patchelf-0.15.2:/nix/store/9vv51km72lpngs6aixxplrr3c88q4c3c-update-autotools-gnu-config-scripts-hook:/nix/store/qd70v8g0561vm8m33kmnp79z00cgyi5n-gcc-wrapper-15.2.0:/nix/store/kfwagnh6i1mysf7vxq679rzh30z9zj3g-binutils-wrapper-2.46:/nix/store/785jidgnryzj566s25s3rb262d4g5znb-nodejs-24.14.1:/nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env:/nix/store/cifzx7qr3mpcphz1bnlww4llshrvczyg-pandoc-cli-3.7.0.2:/nix/store/0rn2xh3zciwdr8sjg79ir79dbr6lnmfb-gnumake-4.4.1:/nix/store/04ys3zgcil28yj4afyk6p3dlrfv60s1h-time-1.10:/nix/store/rhp41khpds0m218gdp4lagkhb957mi42-poppler-utils-25.10.0-dev:/nix/store/3yl2s5r3yph88imzbgbdrh8pbs9rcjcs-zlib-1.3.2-dev:/nix/store/ixhlv41i2wpl84xgjcks061dz4yssbg3-zlib-1.3.2:/nix/store/r7bp82svf04jqw3x7wnjlyr951jkf85k-freetype-2.14.2-dev:/nix/store/bh64ycxf96cc4v43m77nszmpvbs0pfv7-bzip2-1.0.8-dev:/nix/store/zj6r42syyswkhrr174bzppj3n7xhq936-bzip2-1.0.8-bin:/nix/store/2amncb4zvr32gm5d2i8m6gz29c02cn61-bzip2-1.0.8:/nix/store/1x1msj33z37b65vlxbs51l7i4j92qn9h-brotli-1.2.0-dev:/nix/store/7ff90dag7i173s49c5m614wny2lpps1l-brotli-1.2.0-lib:/nix/store/mj1k1nsdqr0mp9wsnkg7blgh3xf5wssv-brotli-1.2.0:/nix/store/h176f4dhbcpj4lpf8sn28vdqp1mks5jk-libpng-apng-1.6.56-dev:/nix/store/gsn3vddway3289p6mzy5shd1paly8dp4-libpng-apng-1.6.56:/nix/store/zr22ggqbv79yv4y4wv06r4grla9h59yx-freetype-2.14.2:/nix/store/gjg4aagfcn6r96c73rz4rwbclbdqqc6v-fontconfig-2.17.1-dev:/nix/store/v18drszzvspk1wlq06r68nxgpn2b4cvd-fontconfig-2.17.1-bin:/nix/store/bg6ms0vw071g1fdbx2my6bbzsk62p6vd-fontconfig-2.17.1-lib:/nix/store/b63lk3n7piwf7a790c4cy0zinqi184fs-libjpeg-turbo-3.1.4-dev:/nix/store/v70k3ch8rcw9b0la3axqb34dkyxqnx2s-libjpeg-turbo-3.1.4-bin:/nix/store/lsln4vpc8spwmb96vjjmg4yd0krd2r7c-libjpeg-turbo-3.1.4:/nix/store/5q46i43k18sspv8wjpasmrgl5n8y7j1s-openjpeg-2.5.4-dev:/nix/store/nrq3pjzsjd4w9vcpgk4a2wfjlqz4xxzw-openjpeg-2.5.4:/nix/store/8zhjvm4vixgvg089nn4wv7hhxlp7qg2c-cairo-1.18.4-dev:/nix/store/hywlq1sf1prbyrhqwf2sbamazp1hghk1-pixman-0.46.4:/nix/store/1kx6y7spy0q6372hqrvib7mw21gaq5bq-libxext-1.3.7-dev:/nix/store/mvyxqkpyj2mgymljzj9bqi9bmz7ca5fk-xorgproto-2025.1:/nix/store/hd6i8dzybk2jqwqh6frarw30w15yqq9b-libxau-1.0.12-dev:/nix/store/2krkc90x3ch0mgkk48fxlglq14nqapdr-libxau-1.0.12:/nix/store/n1ykqk7ibmp4h5r4x5fng4cn9wjlgj9y-libxext-1.3.7:/nix/store/94m0129pm3jlbg4fj8py92j1vi870m9c-libxrender-0.9.12-dev:/nix/store/4303g76pqhl7r8a2xvci0b4bj47bfbjz-libx11-1.8.13-dev:/nix/store/5m91jqg1526jzsahrgmd37k4ml3nc5l4-libx11-1.8.13:/nix/store/dwavjjnzjmp7901n2s61kw40qw8c5rfc-libxrender-0.9.12:/nix/store/x44m80ahg51pz32dr0j39yzsr7bn7d5v-libxcb-1.17.0-dev:/nix/store/fc1g44pg3i10wfzh3gb4m54pfgclsn76-libxcb-1.17.0:/nix/store/kw0yjwbvw6arwgwaa3p8rz46qsgy4626-glib-2.86.3-dev:/nix/store/lg8kfrcxy4bcwnlwbfn6x3s48k4aawba-libffi-3.5.2-dev:/nix/store/hyai3q7gvdfppw4ky7s2mvhxvfyp5bh7-libffi-3.5.2:/nix/store/ypj27q94ay0ybq9aa14gk0cxjv9d7z4m-gettext-1.0:/nix/store/5722rfnbamx35h5df4wlvlqrmvmaan7i-glibc-iconv-2.42:/nix/store/b9jcqjd8gnxr87p7wc91lmbyd90kzlc1-glib-2.86.3-bin:/nix/store/zcmsivndca5wmam9nwnbjrm0zkgykwfz-glib-2.86.3:/nix/store/hgvr4xvcqm4a06rq5scgcy6nlk5q89gd-cairo-1.18.4:/nix/store/pbyr7jlx85a0vlx623jqjd18cnccb5vv-lcms2-2.18-dev:/nix/store/xiq38z94b68c8dgj7nfx9xlh2984c2mp-lcms2-2.18-bin:/nix/store/3j2yd136zgln9w2hsrvlmazyrhcnfri5-lcms2-2.18:/nix/store/ankisnmp03gzp9m0z4bqy1i2ar23wb48-libtiff-4.7.1-dev:/nix/store/cbdy1d44cqa9j7x0ga72dqsk4p49ih70-libtiff-4.7.1-bin:/nix/store/6w9m0a1v9kx40q341wq4y337s8csqhyn-libtiff-4.7.1:/nix/store/7xvb5060qcf36ncp47wz62rl3fsccv1g-curl-8.19.0-dev:/nix/store/dgdzsx6i729gcp1rrz85zbaacgl86gab-krb5-1.22.1-dev:/nix/store/8cr60j6q7rqmcy4k8l6l1cay9579kd6y-krb5-1.22.1-lib:/nix/store/qp2qzmh67rqy6i36sh3iqznk1akiw4q1-krb5-1.22.1:/nix/store/iaf80mkaj9kfgy3h6hf1xqj7la8acr7y-nghttp2-1.68.1-dev:/nix/store/hms747x82q23p2g6r6kgzqf7li2ryk39-nghttp2-1.68.1-lib:/nix/store/yvxyaqh3bzj7nr64zlr1axyf76fgcszb-nghttp2-1.68.1:/nix/store/d2xhslm8a0b1lk0p4plmyip3i194znhy-nghttp3-1.15.0-dev:/nix/store/133x0z91pizyk8zr4l2ccgqlclpkp1lj-nghttp3-1.15.0:/nix/store/yp754aaxmfqdag95053yax1fdaa4s9ck-ngtcp2-1.22.0-dev:/nix/store/g5sd94mk8w1a0wiipk81ri0prk136d32-ngtcp2-1.22.0:/nix/store/j3ypygy4pwwgkdrkxkhnhxqkwx4yw8zq-libidn2-2.3.8-dev:/nix/store/a327a5lqzwakcs3yjgx4sa1931fph5gf-libidn2-2.3.8-bin:/nix/store/sgswwrxkhdlfskklqp4gsbi2cskfg07c-libidn2-2.3.8:/nix/store/dy64cxaygvmjfznysgxk501yds8jij6s-openssl-3.6.1-dev:/nix/store/2di90l89y2ygdy3rbws7dhg9nrvd3pnx-openssl-3.6.1-bin:/nix/store/wbyqkb1vpm41s4jb8pv0i9h4jv08xdrv-openssl-3.6.1:/nix/store/ylldnaarbvwkvpn5dasnjjyvvghh6k3r-libpsl-0.21.5-dev:/nix/store/g6q58mbnmi0f05xpm9nfvfhq963yv7wv-publicsuffix-list-0-unstable-2026-03-26:/nix/store/79kr7fafcvvmch13cyczpckz40159pk5-libpsl-0.21.5:/nix/store/5c04s19in4y2ij0zzkh4y9gqys8rwgc4-libssh2-1.11.1-dev:/nix/store/9lzm6krq5ikzbqbmazbh5jmzwph99rz3-libssh2-1.11.1:/nix/store/vbqakw4shfcbmdxs6kkp3jmp9k5br94y-zstd-1.5.7-dev:/nix/store/91jddg4g6788ilnk3kww8j8jhxhzk6d3-zstd-1.5.7-bin:/nix/store/k0rqiflg1vkn1kj96br5pfxj40p3srz4-zstd-1.5.7:/nix/store/sm2nq18jjqp4x0sxpl6lrvwl9rx6mvj2-curl-8.19.0-bin:/nix/store/pz6b64891m180yb4hadj1jjg3wm3ybng-curl-8.19.0:/nix/store/xafb1qxw69j6fg1s8ln2drppm2zjjfr5-nss-3.112.3-dev:/nix/store/3qfr4jp73jac5rnkx8xj58whv4yc80zy-nspr-4.38.2-dev:/nix/store/amjf7cch3hb5r6l646mwjhrr9384ks4s-nspr-4.38.2:/nix/store/0wnl2h5xgy1q7bgkqdbiyzxnrq3cmigi-nss-3.112.3:/nix/store/92ipcswac970qz2iq0nn1yw1jj69xm69-poppler-utils-25.10.0:/nix/store/l7nryi3685lc6di1wbyfmb5q3v3xmfqz-ghostscript-with-X-10.06.0:/nix/store/hn59rqwq5j0z7l13yns903l6ibylwz1g-imagemagick-7.1.2-19-dev:/nix/store/vd0i6w0g7wgj621lpzc2dsld42fsvh6c-libxt-1.3.1-dev:/nix/store/sl65d0g3k4f6v5w7xclx334zzcj1w533-libsm-1.2.6-dev:/nix/store/07rdpwd0gxa48k7p7p9mk6h0s0p5zknc-libice-1.1.2-dev:/nix/store/qhw8zihdm481cvia6pd0kl2fmqk9mr2k-libice-1.1.2:/nix/store/wnmwabsnj34j46c579y0ypc29xjfxjwf-libsm-1.2.6:/nix/store/vqisl3q8b600dhrpj2a12bk4r5vzn3g4-libxt-1.3.1:/nix/store/vdz5z5d4qvsfqdafihrfwzi5r7wr24lk-libwebp-1.6.0:/nix/store/wgz6lg6jd6rq3n7gxgaj8i9qm6f5xlbf-fftw-double-3.3.10-dev:/nix/store/84crpkdlv33nx4kahqzkss83fvpp8x3q-fftw-double-3.3.10:/nix/store/pjcg9z9zj4hqa7y8jjgsx06rc31q6r8s-imagemagick-7.1.2-19:/nix/store/p8x5zv9s9qg3ld8b7jdm03hkpdqybjl9-jq-1.8.1-dev:/nix/store/v5c3inhfq6xshmwg1c254vfbcy4jp3k9-jq-1.8.1-bin:/nix/store/09bq2i0kb008ccg3qdbyxv81ggxxnn09-jq-1.8.1:/nix/store/9xkb4la9kpnsbrs3kw2cij3wjfbv6j6g-duckdb-1.5.2-dev:/nix/store/kqjjmmq70c07hpizbd2sprryrx6a7bs5-duckdb-1.5.2-lib:/nix/store/n4h91v3p9v5hfgcrmfashil26nsrsrhs-duckdb-1.5.2:/nix/store/jx6bzribg9fa0mxbr8b602rq74k24dr7-python3.13-yamllint-1.37.1:/nix/store/jl0mxihyizv77l66mzbvmv49iiri72sd-python3.13-pyyaml-6.0.3:/nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12:/nix/store/pdjdz9mqsj6az0znlrgh2fj6wp1rb032-python3.13-pathspec-0.12.1:/nix/store/09hk83dw55dpbw1f8km58pycmbfr186k-shellcheck-0.11.0:/nix/store/7xiiq153kv13wcqb6j5zffz2g778nssv-shellcheck-0.11.0-bin:/nix/store/hn7cpgmj18mx8lj5wsnjgcy158cnfyz1-statix-0.5.8:/nix/store/ivy6wb23x19x29qz49y98amkch1jbz84-elan-4.2.1:/nix/store/xiy3ydpzw5bdqqd7ri8qbg3bn4r2qxg1-rustup-1.29.0:/nix/store/biagcw4fwc90ala8pxbdb919khj39rzy-clang-wrapper-19.1.7:/nix/store/vr4sjc5ajni6j76wqkvkx84q141270ak-binutils-wrapper-2.46:/nix/store/xswd8j43wkqpadsgfl3cnf1hibvwncrw-lld-19.1.7-dev:/nix/store/477l7v6l11yw7vc1gzmv8ybjl8rs799z-lld-19.1.7-lib:/nix/store/hvihdgv65b31lrw3rdybjz1m8q314qyi-lld-19.1.7:/nix/store/v2i1hgv567g3v91im5x4g5bff52143i0-cmake-4.1.2:/nix/store/v7mjkia7ki79s5i24ldbzq1khalhgzk0-pkg-config-wrapper-0.29.2:/nix/store/fszv4kq85ywrpq6dy2wydl1ggkbc6sjp-emscripten-5.0.6:/nix/store/pxhpmfr4qwihzxqam9642a9r7jpvbblr-typescript-5.9.3:/nix/store/246dw7jxjgznw9fql388hj43yyknlqmn-vscode-1.116.0:/nix/store/9lhr1c3l9qzv8pzp3idmii1nwvxxjys3-gzip-1.14:/nix/store/x78aqw188hv2nmj8hbbl4q9knhns4qf2-xz-5.8.3-dev:/nix/store/2nm5c858fh52s6mhcffm07s3biaxys44-xz-5.8.3-bin:/nix/store/hmslvsxvs2ijb7iw5krdckai2im6vp2y-xz-5.8.3:/nix/store/i7arixgp0p933iicqzfza1dm9g2vgbzf-lz4-1.10.0-dev:/nix/store/fy28r1ynjk65gnj898k9dabyvzz9mryc-lz4-1.10.0-lib:/nix/store/m7m89ms25namgzbhcx6nf42jgjx55lcx-lz4-1.10.0:/nix/store/qpf8bnaad0j8g4ggl65hvfs8l5y1alwp-mermaid-cli-11.12.0:/nix/store/nkai8ssk915yc9mvj0xi28zliwwsaacp-zpaq-7.15:/nix/store/0l71d5r282xjml5zhd3knf4syinczqwh-R-4.5.3-wrapper:/nix/store/sw1dgmpi3s1vkjfbdjwj4bliz626fvqp-compiler-rt-libc-19.1.7-dev:/nix/store/9agl8i5ax5w0x01rsgazhizhgpshb8pg-compiler-rt-libc-19.1.7'
export NIXPKGS_CMAKE_PREFIX_PATH
NIX_BINTOOLS='/nix/store/kfwagnh6i1mysf7vxq679rzh30z9zj3g-binutils-wrapper-2.46'
export NIX_BINTOOLS
NIX_BINTOOLS_FOR_TARGET='/nix/store/vr4sjc5ajni6j76wqkvkx84q141270ak-binutils-wrapper-2.46'
export NIX_BINTOOLS_FOR_TARGET
NIX_BINTOOLS_WRAPPER_TARGET_HOST_x86_64_unknown_linux_gnu='1'
export NIX_BINTOOLS_WRAPPER_TARGET_HOST_x86_64_unknown_linux_gnu
NIX_BINTOOLS_WRAPPER_TARGET_TARGET_x86_64_unknown_linux_gnu='1'
export NIX_BINTOOLS_WRAPPER_TARGET_TARGET_x86_64_unknown_linux_gnu
NIX_BUILD_CORES='16'
export NIX_BUILD_CORES
NIX_CC='/nix/store/qd70v8g0561vm8m33kmnp79z00cgyi5n-gcc-wrapper-15.2.0'
export NIX_CC
NIX_CC_FOR_TARGET='/nix/store/biagcw4fwc90ala8pxbdb919khj39rzy-clang-wrapper-19.1.7'
export NIX_CC_FOR_TARGET
NIX_CC_WRAPPER_TARGET_HOST_x86_64_unknown_linux_gnu='1'
export NIX_CC_WRAPPER_TARGET_HOST_x86_64_unknown_linux_gnu
NIX_CC_WRAPPER_TARGET_TARGET_x86_64_unknown_linux_gnu='1'
export NIX_CC_WRAPPER_TARGET_TARGET_x86_64_unknown_linux_gnu
NIX_CFLAGS_COMPILE=' -frandom-seed=9x8v2c9sfn -isystem /nix/store/785jidgnryzj566s25s3rb262d4g5znb-nodejs-24.14.1/include -fmacro-prefix-map=/nix/store/785jidgnryzj566s25s3rb262d4g5znb-nodejs-24.14.1=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-nodejs-24.14.1 -isystem /nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env/include -fmacro-prefix-map=/nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-python3-3.13.12-env -isystem /nix/store/0rn2xh3zciwdr8sjg79ir79dbr6lnmfb-gnumake-4.4.1/include -fmacro-prefix-map=/nix/store/0rn2xh3zciwdr8sjg79ir79dbr6lnmfb-gnumake-4.4.1=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-gnumake-4.4.1 -isystem /nix/store/rhp41khpds0m218gdp4lagkhb957mi42-poppler-utils-25.10.0-dev/include -fmacro-prefix-map=/nix/store/rhp41khpds0m218gdp4lagkhb957mi42-poppler-utils-25.10.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-poppler-utils-25.10.0-dev -isystem /nix/store/3yl2s5r3yph88imzbgbdrh8pbs9rcjcs-zlib-1.3.2-dev/include -fmacro-prefix-map=/nix/store/3yl2s5r3yph88imzbgbdrh8pbs9rcjcs-zlib-1.3.2-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-zlib-1.3.2-dev -isystem /nix/store/r7bp82svf04jqw3x7wnjlyr951jkf85k-freetype-2.14.2-dev/include -fmacro-prefix-map=/nix/store/r7bp82svf04jqw3x7wnjlyr951jkf85k-freetype-2.14.2-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-freetype-2.14.2-dev -isystem /nix/store/bh64ycxf96cc4v43m77nszmpvbs0pfv7-bzip2-1.0.8-dev/include -fmacro-prefix-map=/nix/store/bh64ycxf96cc4v43m77nszmpvbs0pfv7-bzip2-1.0.8-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-bzip2-1.0.8-dev -isystem /nix/store/1x1msj33z37b65vlxbs51l7i4j92qn9h-brotli-1.2.0-dev/include -fmacro-prefix-map=/nix/store/1x1msj33z37b65vlxbs51l7i4j92qn9h-brotli-1.2.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-brotli-1.2.0-dev -isystem /nix/store/h176f4dhbcpj4lpf8sn28vdqp1mks5jk-libpng-apng-1.6.56-dev/include -fmacro-prefix-map=/nix/store/h176f4dhbcpj4lpf8sn28vdqp1mks5jk-libpng-apng-1.6.56-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libpng-apng-1.6.56-dev -isystem /nix/store/gjg4aagfcn6r96c73rz4rwbclbdqqc6v-fontconfig-2.17.1-dev/include -fmacro-prefix-map=/nix/store/gjg4aagfcn6r96c73rz4rwbclbdqqc6v-fontconfig-2.17.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-fontconfig-2.17.1-dev -isystem /nix/store/b63lk3n7piwf7a790c4cy0zinqi184fs-libjpeg-turbo-3.1.4-dev/include -fmacro-prefix-map=/nix/store/b63lk3n7piwf7a790c4cy0zinqi184fs-libjpeg-turbo-3.1.4-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libjpeg-turbo-3.1.4-dev -isystem /nix/store/5q46i43k18sspv8wjpasmrgl5n8y7j1s-openjpeg-2.5.4-dev/include -fmacro-prefix-map=/nix/store/5q46i43k18sspv8wjpasmrgl5n8y7j1s-openjpeg-2.5.4-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-openjpeg-2.5.4-dev -isystem /nix/store/8zhjvm4vixgvg089nn4wv7hhxlp7qg2c-cairo-1.18.4-dev/include -fmacro-prefix-map=/nix/store/8zhjvm4vixgvg089nn4wv7hhxlp7qg2c-cairo-1.18.4-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-cairo-1.18.4-dev -isystem /nix/store/hywlq1sf1prbyrhqwf2sbamazp1hghk1-pixman-0.46.4/include -fmacro-prefix-map=/nix/store/hywlq1sf1prbyrhqwf2sbamazp1hghk1-pixman-0.46.4=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-pixman-0.46.4 -isystem /nix/store/1kx6y7spy0q6372hqrvib7mw21gaq5bq-libxext-1.3.7-dev/include -fmacro-prefix-map=/nix/store/1kx6y7spy0q6372hqrvib7mw21gaq5bq-libxext-1.3.7-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libxext-1.3.7-dev -isystem /nix/store/mvyxqkpyj2mgymljzj9bqi9bmz7ca5fk-xorgproto-2025.1/include -fmacro-prefix-map=/nix/store/mvyxqkpyj2mgymljzj9bqi9bmz7ca5fk-xorgproto-2025.1=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-xorgproto-2025.1 -isystem /nix/store/hd6i8dzybk2jqwqh6frarw30w15yqq9b-libxau-1.0.12-dev/include -fmacro-prefix-map=/nix/store/hd6i8dzybk2jqwqh6frarw30w15yqq9b-libxau-1.0.12-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libxau-1.0.12-dev -isystem /nix/store/94m0129pm3jlbg4fj8py92j1vi870m9c-libxrender-0.9.12-dev/include -fmacro-prefix-map=/nix/store/94m0129pm3jlbg4fj8py92j1vi870m9c-libxrender-0.9.12-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libxrender-0.9.12-dev -isystem /nix/store/4303g76pqhl7r8a2xvci0b4bj47bfbjz-libx11-1.8.13-dev/include -fmacro-prefix-map=/nix/store/4303g76pqhl7r8a2xvci0b4bj47bfbjz-libx11-1.8.13-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libx11-1.8.13-dev -isystem /nix/store/x44m80ahg51pz32dr0j39yzsr7bn7d5v-libxcb-1.17.0-dev/include -fmacro-prefix-map=/nix/store/x44m80ahg51pz32dr0j39yzsr7bn7d5v-libxcb-1.17.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libxcb-1.17.0-dev -isystem /nix/store/kw0yjwbvw6arwgwaa3p8rz46qsgy4626-glib-2.86.3-dev/include -fmacro-prefix-map=/nix/store/kw0yjwbvw6arwgwaa3p8rz46qsgy4626-glib-2.86.3-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-glib-2.86.3-dev -isystem /nix/store/lg8kfrcxy4bcwnlwbfn6x3s48k4aawba-libffi-3.5.2-dev/include -fmacro-prefix-map=/nix/store/lg8kfrcxy4bcwnlwbfn6x3s48k4aawba-libffi-3.5.2-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libffi-3.5.2-dev -isystem /nix/store/ypj27q94ay0ybq9aa14gk0cxjv9d7z4m-gettext-1.0/include -fmacro-prefix-map=/nix/store/ypj27q94ay0ybq9aa14gk0cxjv9d7z4m-gettext-1.0=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-gettext-1.0 -isystem /nix/store/5722rfnbamx35h5df4wlvlqrmvmaan7i-glibc-iconv-2.42/include -fmacro-prefix-map=/nix/store/5722rfnbamx35h5df4wlvlqrmvmaan7i-glibc-iconv-2.42=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-glibc-iconv-2.42 -isystem /nix/store/pbyr7jlx85a0vlx623jqjd18cnccb5vv-lcms2-2.18-dev/include -fmacro-prefix-map=/nix/store/pbyr7jlx85a0vlx623jqjd18cnccb5vv-lcms2-2.18-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-lcms2-2.18-dev -isystem /nix/store/ankisnmp03gzp9m0z4bqy1i2ar23wb48-libtiff-4.7.1-dev/include -fmacro-prefix-map=/nix/store/ankisnmp03gzp9m0z4bqy1i2ar23wb48-libtiff-4.7.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libtiff-4.7.1-dev -isystem /nix/store/7xvb5060qcf36ncp47wz62rl3fsccv1g-curl-8.19.0-dev/include -fmacro-prefix-map=/nix/store/7xvb5060qcf36ncp47wz62rl3fsccv1g-curl-8.19.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-curl-8.19.0-dev -isystem /nix/store/dgdzsx6i729gcp1rrz85zbaacgl86gab-krb5-1.22.1-dev/include -fmacro-prefix-map=/nix/store/dgdzsx6i729gcp1rrz85zbaacgl86gab-krb5-1.22.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-krb5-1.22.1-dev -isystem /nix/store/iaf80mkaj9kfgy3h6hf1xqj7la8acr7y-nghttp2-1.68.1-dev/include -fmacro-prefix-map=/nix/store/iaf80mkaj9kfgy3h6hf1xqj7la8acr7y-nghttp2-1.68.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-nghttp2-1.68.1-dev -isystem /nix/store/d2xhslm8a0b1lk0p4plmyip3i194znhy-nghttp3-1.15.0-dev/include -fmacro-prefix-map=/nix/store/d2xhslm8a0b1lk0p4plmyip3i194znhy-nghttp3-1.15.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-nghttp3-1.15.0-dev -isystem /nix/store/yp754aaxmfqdag95053yax1fdaa4s9ck-ngtcp2-1.22.0-dev/include -fmacro-prefix-map=/nix/store/yp754aaxmfqdag95053yax1fdaa4s9ck-ngtcp2-1.22.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-ngtcp2-1.22.0-dev -isystem /nix/store/j3ypygy4pwwgkdrkxkhnhxqkwx4yw8zq-libidn2-2.3.8-dev/include -fmacro-prefix-map=/nix/store/j3ypygy4pwwgkdrkxkhnhxqkwx4yw8zq-libidn2-2.3.8-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libidn2-2.3.8-dev -isystem /nix/store/dy64cxaygvmjfznysgxk501yds8jij6s-openssl-3.6.1-dev/include -fmacro-prefix-map=/nix/store/dy64cxaygvmjfznysgxk501yds8jij6s-openssl-3.6.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-openssl-3.6.1-dev -isystem /nix/store/ylldnaarbvwkvpn5dasnjjyvvghh6k3r-libpsl-0.21.5-dev/include -fmacro-prefix-map=/nix/store/ylldnaarbvwkvpn5dasnjjyvvghh6k3r-libpsl-0.21.5-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libpsl-0.21.5-dev -isystem /nix/store/5c04s19in4y2ij0zzkh4y9gqys8rwgc4-libssh2-1.11.1-dev/include -fmacro-prefix-map=/nix/store/5c04s19in4y2ij0zzkh4y9gqys8rwgc4-libssh2-1.11.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libssh2-1.11.1-dev -isystem /nix/store/vbqakw4shfcbmdxs6kkp3jmp9k5br94y-zstd-1.5.7-dev/include -fmacro-prefix-map=/nix/store/vbqakw4shfcbmdxs6kkp3jmp9k5br94y-zstd-1.5.7-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-zstd-1.5.7-dev -isystem /nix/store/xafb1qxw69j6fg1s8ln2drppm2zjjfr5-nss-3.112.3-dev/include -fmacro-prefix-map=/nix/store/xafb1qxw69j6fg1s8ln2drppm2zjjfr5-nss-3.112.3-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-nss-3.112.3-dev -isystem /nix/store/3qfr4jp73jac5rnkx8xj58whv4yc80zy-nspr-4.38.2-dev/include -fmacro-prefix-map=/nix/store/3qfr4jp73jac5rnkx8xj58whv4yc80zy-nspr-4.38.2-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-nspr-4.38.2-dev -isystem /nix/store/l7nryi3685lc6di1wbyfmb5q3v3xmfqz-ghostscript-with-X-10.06.0/include -fmacro-prefix-map=/nix/store/l7nryi3685lc6di1wbyfmb5q3v3xmfqz-ghostscript-with-X-10.06.0=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-ghostscript-with-X-10.06.0 -isystem /nix/store/hn59rqwq5j0z7l13yns903l6ibylwz1g-imagemagick-7.1.2-19-dev/include -fmacro-prefix-map=/nix/store/hn59rqwq5j0z7l13yns903l6ibylwz1g-imagemagick-7.1.2-19-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-imagemagick-7.1.2-19-dev -isystem /nix/store/vd0i6w0g7wgj621lpzc2dsld42fsvh6c-libxt-1.3.1-dev/include -fmacro-prefix-map=/nix/store/vd0i6w0g7wgj621lpzc2dsld42fsvh6c-libxt-1.3.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libxt-1.3.1-dev -isystem /nix/store/sl65d0g3k4f6v5w7xclx334zzcj1w533-libsm-1.2.6-dev/include -fmacro-prefix-map=/nix/store/sl65d0g3k4f6v5w7xclx334zzcj1w533-libsm-1.2.6-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libsm-1.2.6-dev -isystem /nix/store/07rdpwd0gxa48k7p7p9mk6h0s0p5zknc-libice-1.1.2-dev/include -fmacro-prefix-map=/nix/store/07rdpwd0gxa48k7p7p9mk6h0s0p5zknc-libice-1.1.2-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libice-1.1.2-dev -isystem /nix/store/vdz5z5d4qvsfqdafihrfwzi5r7wr24lk-libwebp-1.6.0/include -fmacro-prefix-map=/nix/store/vdz5z5d4qvsfqdafihrfwzi5r7wr24lk-libwebp-1.6.0=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libwebp-1.6.0 -isystem /nix/store/wgz6lg6jd6rq3n7gxgaj8i9qm6f5xlbf-fftw-double-3.3.10-dev/include -fmacro-prefix-map=/nix/store/wgz6lg6jd6rq3n7gxgaj8i9qm6f5xlbf-fftw-double-3.3.10-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-fftw-double-3.3.10-dev -isystem /nix/store/p8x5zv9s9qg3ld8b7jdm03hkpdqybjl9-jq-1.8.1-dev/include -fmacro-prefix-map=/nix/store/p8x5zv9s9qg3ld8b7jdm03hkpdqybjl9-jq-1.8.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-jq-1.8.1-dev -isystem /nix/store/9xkb4la9kpnsbrs3kw2cij3wjfbv6j6g-duckdb-1.5.2-dev/include -fmacro-prefix-map=/nix/store/9xkb4la9kpnsbrs3kw2cij3wjfbv6j6g-duckdb-1.5.2-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-duckdb-1.5.2-dev -isystem /nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12/include -fmacro-prefix-map=/nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-python3-3.13.12 -isystem /nix/store/xswd8j43wkqpadsgfl3cnf1hibvwncrw-lld-19.1.7-dev/include -fmacro-prefix-map=/nix/store/xswd8j43wkqpadsgfl3cnf1hibvwncrw-lld-19.1.7-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-lld-19.1.7-dev -isystem /nix/store/x78aqw188hv2nmj8hbbl4q9knhns4qf2-xz-5.8.3-dev/include -fmacro-prefix-map=/nix/store/x78aqw188hv2nmj8hbbl4q9knhns4qf2-xz-5.8.3-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-xz-5.8.3-dev -isystem /nix/store/i7arixgp0p933iicqzfza1dm9g2vgbzf-lz4-1.10.0-dev/include -fmacro-prefix-map=/nix/store/i7arixgp0p933iicqzfza1dm9g2vgbzf-lz4-1.10.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-lz4-1.10.0-dev -isystem /nix/store/sw1dgmpi3s1vkjfbdjwj4bliz626fvqp-compiler-rt-libc-19.1.7-dev/include -fmacro-prefix-map=/nix/store/sw1dgmpi3s1vkjfbdjwj4bliz626fvqp-compiler-rt-libc-19.1.7-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-compiler-rt-libc-19.1.7-dev -isystem /nix/store/785jidgnryzj566s25s3rb262d4g5znb-nodejs-24.14.1/include -fmacro-prefix-map=/nix/store/785jidgnryzj566s25s3rb262d4g5znb-nodejs-24.14.1=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-nodejs-24.14.1 -isystem /nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env/include -fmacro-prefix-map=/nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-python3-3.13.12-env -isystem /nix/store/0rn2xh3zciwdr8sjg79ir79dbr6lnmfb-gnumake-4.4.1/include -fmacro-prefix-map=/nix/store/0rn2xh3zciwdr8sjg79ir79dbr6lnmfb-gnumake-4.4.1=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-gnumake-4.4.1 -isystem /nix/store/rhp41khpds0m218gdp4lagkhb957mi42-poppler-utils-25.10.0-dev/include -fmacro-prefix-map=/nix/store/rhp41khpds0m218gdp4lagkhb957mi42-poppler-utils-25.10.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-poppler-utils-25.10.0-dev -isystem /nix/store/3yl2s5r3yph88imzbgbdrh8pbs9rcjcs-zlib-1.3.2-dev/include -fmacro-prefix-map=/nix/store/3yl2s5r3yph88imzbgbdrh8pbs9rcjcs-zlib-1.3.2-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-zlib-1.3.2-dev -isystem /nix/store/r7bp82svf04jqw3x7wnjlyr951jkf85k-freetype-2.14.2-dev/include -fmacro-prefix-map=/nix/store/r7bp82svf04jqw3x7wnjlyr951jkf85k-freetype-2.14.2-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-freetype-2.14.2-dev -isystem /nix/store/bh64ycxf96cc4v43m77nszmpvbs0pfv7-bzip2-1.0.8-dev/include -fmacro-prefix-map=/nix/store/bh64ycxf96cc4v43m77nszmpvbs0pfv7-bzip2-1.0.8-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-bzip2-1.0.8-dev -isystem /nix/store/1x1msj33z37b65vlxbs51l7i4j92qn9h-brotli-1.2.0-dev/include -fmacro-prefix-map=/nix/store/1x1msj33z37b65vlxbs51l7i4j92qn9h-brotli-1.2.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-brotli-1.2.0-dev -isystem /nix/store/h176f4dhbcpj4lpf8sn28vdqp1mks5jk-libpng-apng-1.6.56-dev/include -fmacro-prefix-map=/nix/store/h176f4dhbcpj4lpf8sn28vdqp1mks5jk-libpng-apng-1.6.56-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libpng-apng-1.6.56-dev -isystem /nix/store/gjg4aagfcn6r96c73rz4rwbclbdqqc6v-fontconfig-2.17.1-dev/include -fmacro-prefix-map=/nix/store/gjg4aagfcn6r96c73rz4rwbclbdqqc6v-fontconfig-2.17.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-fontconfig-2.17.1-dev -isystem /nix/store/b63lk3n7piwf7a790c4cy0zinqi184fs-libjpeg-turbo-3.1.4-dev/include -fmacro-prefix-map=/nix/store/b63lk3n7piwf7a790c4cy0zinqi184fs-libjpeg-turbo-3.1.4-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libjpeg-turbo-3.1.4-dev -isystem /nix/store/5q46i43k18sspv8wjpasmrgl5n8y7j1s-openjpeg-2.5.4-dev/include -fmacro-prefix-map=/nix/store/5q46i43k18sspv8wjpasmrgl5n8y7j1s-openjpeg-2.5.4-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-openjpeg-2.5.4-dev -isystem /nix/store/8zhjvm4vixgvg089nn4wv7hhxlp7qg2c-cairo-1.18.4-dev/include -fmacro-prefix-map=/nix/store/8zhjvm4vixgvg089nn4wv7hhxlp7qg2c-cairo-1.18.4-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-cairo-1.18.4-dev -isystem /nix/store/hywlq1sf1prbyrhqwf2sbamazp1hghk1-pixman-0.46.4/include -fmacro-prefix-map=/nix/store/hywlq1sf1prbyrhqwf2sbamazp1hghk1-pixman-0.46.4=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-pixman-0.46.4 -isystem /nix/store/1kx6y7spy0q6372hqrvib7mw21gaq5bq-libxext-1.3.7-dev/include -fmacro-prefix-map=/nix/store/1kx6y7spy0q6372hqrvib7mw21gaq5bq-libxext-1.3.7-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libxext-1.3.7-dev -isystem /nix/store/mvyxqkpyj2mgymljzj9bqi9bmz7ca5fk-xorgproto-2025.1/include -fmacro-prefix-map=/nix/store/mvyxqkpyj2mgymljzj9bqi9bmz7ca5fk-xorgproto-2025.1=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-xorgproto-2025.1 -isystem /nix/store/hd6i8dzybk2jqwqh6frarw30w15yqq9b-libxau-1.0.12-dev/include -fmacro-prefix-map=/nix/store/hd6i8dzybk2jqwqh6frarw30w15yqq9b-libxau-1.0.12-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libxau-1.0.12-dev -isystem /nix/store/94m0129pm3jlbg4fj8py92j1vi870m9c-libxrender-0.9.12-dev/include -fmacro-prefix-map=/nix/store/94m0129pm3jlbg4fj8py92j1vi870m9c-libxrender-0.9.12-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libxrender-0.9.12-dev -isystem /nix/store/4303g76pqhl7r8a2xvci0b4bj47bfbjz-libx11-1.8.13-dev/include -fmacro-prefix-map=/nix/store/4303g76pqhl7r8a2xvci0b4bj47bfbjz-libx11-1.8.13-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libx11-1.8.13-dev -isystem /nix/store/x44m80ahg51pz32dr0j39yzsr7bn7d5v-libxcb-1.17.0-dev/include -fmacro-prefix-map=/nix/store/x44m80ahg51pz32dr0j39yzsr7bn7d5v-libxcb-1.17.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libxcb-1.17.0-dev -isystem /nix/store/kw0yjwbvw6arwgwaa3p8rz46qsgy4626-glib-2.86.3-dev/include -fmacro-prefix-map=/nix/store/kw0yjwbvw6arwgwaa3p8rz46qsgy4626-glib-2.86.3-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-glib-2.86.3-dev -isystem /nix/store/lg8kfrcxy4bcwnlwbfn6x3s48k4aawba-libffi-3.5.2-dev/include -fmacro-prefix-map=/nix/store/lg8kfrcxy4bcwnlwbfn6x3s48k4aawba-libffi-3.5.2-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libffi-3.5.2-dev -isystem /nix/store/ypj27q94ay0ybq9aa14gk0cxjv9d7z4m-gettext-1.0/include -fmacro-prefix-map=/nix/store/ypj27q94ay0ybq9aa14gk0cxjv9d7z4m-gettext-1.0=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-gettext-1.0 -isystem /nix/store/5722rfnbamx35h5df4wlvlqrmvmaan7i-glibc-iconv-2.42/include -fmacro-prefix-map=/nix/store/5722rfnbamx35h5df4wlvlqrmvmaan7i-glibc-iconv-2.42=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-glibc-iconv-2.42 -isystem /nix/store/pbyr7jlx85a0vlx623jqjd18cnccb5vv-lcms2-2.18-dev/include -fmacro-prefix-map=/nix/store/pbyr7jlx85a0vlx623jqjd18cnccb5vv-lcms2-2.18-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-lcms2-2.18-dev -isystem /nix/store/ankisnmp03gzp9m0z4bqy1i2ar23wb48-libtiff-4.7.1-dev/include -fmacro-prefix-map=/nix/store/ankisnmp03gzp9m0z4bqy1i2ar23wb48-libtiff-4.7.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libtiff-4.7.1-dev -isystem /nix/store/7xvb5060qcf36ncp47wz62rl3fsccv1g-curl-8.19.0-dev/include -fmacro-prefix-map=/nix/store/7xvb5060qcf36ncp47wz62rl3fsccv1g-curl-8.19.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-curl-8.19.0-dev -isystem /nix/store/dgdzsx6i729gcp1rrz85zbaacgl86gab-krb5-1.22.1-dev/include -fmacro-prefix-map=/nix/store/dgdzsx6i729gcp1rrz85zbaacgl86gab-krb5-1.22.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-krb5-1.22.1-dev -isystem /nix/store/iaf80mkaj9kfgy3h6hf1xqj7la8acr7y-nghttp2-1.68.1-dev/include -fmacro-prefix-map=/nix/store/iaf80mkaj9kfgy3h6hf1xqj7la8acr7y-nghttp2-1.68.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-nghttp2-1.68.1-dev -isystem /nix/store/d2xhslm8a0b1lk0p4plmyip3i194znhy-nghttp3-1.15.0-dev/include -fmacro-prefix-map=/nix/store/d2xhslm8a0b1lk0p4plmyip3i194znhy-nghttp3-1.15.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-nghttp3-1.15.0-dev -isystem /nix/store/yp754aaxmfqdag95053yax1fdaa4s9ck-ngtcp2-1.22.0-dev/include -fmacro-prefix-map=/nix/store/yp754aaxmfqdag95053yax1fdaa4s9ck-ngtcp2-1.22.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-ngtcp2-1.22.0-dev -isystem /nix/store/j3ypygy4pwwgkdrkxkhnhxqkwx4yw8zq-libidn2-2.3.8-dev/include -fmacro-prefix-map=/nix/store/j3ypygy4pwwgkdrkxkhnhxqkwx4yw8zq-libidn2-2.3.8-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libidn2-2.3.8-dev -isystem /nix/store/dy64cxaygvmjfznysgxk501yds8jij6s-openssl-3.6.1-dev/include -fmacro-prefix-map=/nix/store/dy64cxaygvmjfznysgxk501yds8jij6s-openssl-3.6.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-openssl-3.6.1-dev -isystem /nix/store/ylldnaarbvwkvpn5dasnjjyvvghh6k3r-libpsl-0.21.5-dev/include -fmacro-prefix-map=/nix/store/ylldnaarbvwkvpn5dasnjjyvvghh6k3r-libpsl-0.21.5-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libpsl-0.21.5-dev -isystem /nix/store/5c04s19in4y2ij0zzkh4y9gqys8rwgc4-libssh2-1.11.1-dev/include -fmacro-prefix-map=/nix/store/5c04s19in4y2ij0zzkh4y9gqys8rwgc4-libssh2-1.11.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libssh2-1.11.1-dev -isystem /nix/store/vbqakw4shfcbmdxs6kkp3jmp9k5br94y-zstd-1.5.7-dev/include -fmacro-prefix-map=/nix/store/vbqakw4shfcbmdxs6kkp3jmp9k5br94y-zstd-1.5.7-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-zstd-1.5.7-dev -isystem /nix/store/xafb1qxw69j6fg1s8ln2drppm2zjjfr5-nss-3.112.3-dev/include -fmacro-prefix-map=/nix/store/xafb1qxw69j6fg1s8ln2drppm2zjjfr5-nss-3.112.3-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-nss-3.112.3-dev -isystem /nix/store/3qfr4jp73jac5rnkx8xj58whv4yc80zy-nspr-4.38.2-dev/include -fmacro-prefix-map=/nix/store/3qfr4jp73jac5rnkx8xj58whv4yc80zy-nspr-4.38.2-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-nspr-4.38.2-dev -isystem /nix/store/l7nryi3685lc6di1wbyfmb5q3v3xmfqz-ghostscript-with-X-10.06.0/include -fmacro-prefix-map=/nix/store/l7nryi3685lc6di1wbyfmb5q3v3xmfqz-ghostscript-with-X-10.06.0=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-ghostscript-with-X-10.06.0 -isystem /nix/store/hn59rqwq5j0z7l13yns903l6ibylwz1g-imagemagick-7.1.2-19-dev/include -fmacro-prefix-map=/nix/store/hn59rqwq5j0z7l13yns903l6ibylwz1g-imagemagick-7.1.2-19-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-imagemagick-7.1.2-19-dev -isystem /nix/store/vd0i6w0g7wgj621lpzc2dsld42fsvh6c-libxt-1.3.1-dev/include -fmacro-prefix-map=/nix/store/vd0i6w0g7wgj621lpzc2dsld42fsvh6c-libxt-1.3.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libxt-1.3.1-dev -isystem /nix/store/sl65d0g3k4f6v5w7xclx334zzcj1w533-libsm-1.2.6-dev/include -fmacro-prefix-map=/nix/store/sl65d0g3k4f6v5w7xclx334zzcj1w533-libsm-1.2.6-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libsm-1.2.6-dev -isystem /nix/store/07rdpwd0gxa48k7p7p9mk6h0s0p5zknc-libice-1.1.2-dev/include -fmacro-prefix-map=/nix/store/07rdpwd0gxa48k7p7p9mk6h0s0p5zknc-libice-1.1.2-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libice-1.1.2-dev -isystem /nix/store/vdz5z5d4qvsfqdafihrfwzi5r7wr24lk-libwebp-1.6.0/include -fmacro-prefix-map=/nix/store/vdz5z5d4qvsfqdafihrfwzi5r7wr24lk-libwebp-1.6.0=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libwebp-1.6.0 -isystem /nix/store/wgz6lg6jd6rq3n7gxgaj8i9qm6f5xlbf-fftw-double-3.3.10-dev/include -fmacro-prefix-map=/nix/store/wgz6lg6jd6rq3n7gxgaj8i9qm6f5xlbf-fftw-double-3.3.10-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-fftw-double-3.3.10-dev -isystem /nix/store/p8x5zv9s9qg3ld8b7jdm03hkpdqybjl9-jq-1.8.1-dev/include -fmacro-prefix-map=/nix/store/p8x5zv9s9qg3ld8b7jdm03hkpdqybjl9-jq-1.8.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-jq-1.8.1-dev -isystem /nix/store/9xkb4la9kpnsbrs3kw2cij3wjfbv6j6g-duckdb-1.5.2-dev/include -fmacro-prefix-map=/nix/store/9xkb4la9kpnsbrs3kw2cij3wjfbv6j6g-duckdb-1.5.2-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-duckdb-1.5.2-dev -isystem /nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12/include -fmacro-prefix-map=/nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-python3-3.13.12 -isystem /nix/store/xswd8j43wkqpadsgfl3cnf1hibvwncrw-lld-19.1.7-dev/include -fmacro-prefix-map=/nix/store/xswd8j43wkqpadsgfl3cnf1hibvwncrw-lld-19.1.7-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-lld-19.1.7-dev -isystem /nix/store/x78aqw188hv2nmj8hbbl4q9knhns4qf2-xz-5.8.3-dev/include -fmacro-prefix-map=/nix/store/x78aqw188hv2nmj8hbbl4q9knhns4qf2-xz-5.8.3-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-xz-5.8.3-dev -isystem /nix/store/i7arixgp0p933iicqzfza1dm9g2vgbzf-lz4-1.10.0-dev/include -fmacro-prefix-map=/nix/store/i7arixgp0p933iicqzfza1dm9g2vgbzf-lz4-1.10.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-lz4-1.10.0-dev -isystem /nix/store/sw1dgmpi3s1vkjfbdjwj4bliz626fvqp-compiler-rt-libc-19.1.7-dev/include -fmacro-prefix-map=/nix/store/sw1dgmpi3s1vkjfbdjwj4bliz626fvqp-compiler-rt-libc-19.1.7-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-compiler-rt-libc-19.1.7-dev'
export NIX_CFLAGS_COMPILE
NIX_CFLAGS_COMPILE_FOR_TARGET=' -isystem /nix/store/785jidgnryzj566s25s3rb262d4g5znb-nodejs-24.14.1/include -fmacro-prefix-map=/nix/store/785jidgnryzj566s25s3rb262d4g5znb-nodejs-24.14.1=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-nodejs-24.14.1 -isystem /nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env/include -fmacro-prefix-map=/nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-python3-3.13.12-env -isystem /nix/store/0rn2xh3zciwdr8sjg79ir79dbr6lnmfb-gnumake-4.4.1/include -fmacro-prefix-map=/nix/store/0rn2xh3zciwdr8sjg79ir79dbr6lnmfb-gnumake-4.4.1=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-gnumake-4.4.1 -isystem /nix/store/rhp41khpds0m218gdp4lagkhb957mi42-poppler-utils-25.10.0-dev/include -fmacro-prefix-map=/nix/store/rhp41khpds0m218gdp4lagkhb957mi42-poppler-utils-25.10.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-poppler-utils-25.10.0-dev -isystem /nix/store/3yl2s5r3yph88imzbgbdrh8pbs9rcjcs-zlib-1.3.2-dev/include -fmacro-prefix-map=/nix/store/3yl2s5r3yph88imzbgbdrh8pbs9rcjcs-zlib-1.3.2-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-zlib-1.3.2-dev -isystem /nix/store/r7bp82svf04jqw3x7wnjlyr951jkf85k-freetype-2.14.2-dev/include -fmacro-prefix-map=/nix/store/r7bp82svf04jqw3x7wnjlyr951jkf85k-freetype-2.14.2-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-freetype-2.14.2-dev -isystem /nix/store/bh64ycxf96cc4v43m77nszmpvbs0pfv7-bzip2-1.0.8-dev/include -fmacro-prefix-map=/nix/store/bh64ycxf96cc4v43m77nszmpvbs0pfv7-bzip2-1.0.8-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-bzip2-1.0.8-dev -isystem /nix/store/1x1msj33z37b65vlxbs51l7i4j92qn9h-brotli-1.2.0-dev/include -fmacro-prefix-map=/nix/store/1x1msj33z37b65vlxbs51l7i4j92qn9h-brotli-1.2.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-brotli-1.2.0-dev -isystem /nix/store/h176f4dhbcpj4lpf8sn28vdqp1mks5jk-libpng-apng-1.6.56-dev/include -fmacro-prefix-map=/nix/store/h176f4dhbcpj4lpf8sn28vdqp1mks5jk-libpng-apng-1.6.56-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libpng-apng-1.6.56-dev -isystem /nix/store/gjg4aagfcn6r96c73rz4rwbclbdqqc6v-fontconfig-2.17.1-dev/include -fmacro-prefix-map=/nix/store/gjg4aagfcn6r96c73rz4rwbclbdqqc6v-fontconfig-2.17.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-fontconfig-2.17.1-dev -isystem /nix/store/b63lk3n7piwf7a790c4cy0zinqi184fs-libjpeg-turbo-3.1.4-dev/include -fmacro-prefix-map=/nix/store/b63lk3n7piwf7a790c4cy0zinqi184fs-libjpeg-turbo-3.1.4-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libjpeg-turbo-3.1.4-dev -isystem /nix/store/5q46i43k18sspv8wjpasmrgl5n8y7j1s-openjpeg-2.5.4-dev/include -fmacro-prefix-map=/nix/store/5q46i43k18sspv8wjpasmrgl5n8y7j1s-openjpeg-2.5.4-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-openjpeg-2.5.4-dev -isystem /nix/store/8zhjvm4vixgvg089nn4wv7hhxlp7qg2c-cairo-1.18.4-dev/include -fmacro-prefix-map=/nix/store/8zhjvm4vixgvg089nn4wv7hhxlp7qg2c-cairo-1.18.4-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-cairo-1.18.4-dev -isystem /nix/store/hywlq1sf1prbyrhqwf2sbamazp1hghk1-pixman-0.46.4/include -fmacro-prefix-map=/nix/store/hywlq1sf1prbyrhqwf2sbamazp1hghk1-pixman-0.46.4=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-pixman-0.46.4 -isystem /nix/store/1kx6y7spy0q6372hqrvib7mw21gaq5bq-libxext-1.3.7-dev/include -fmacro-prefix-map=/nix/store/1kx6y7spy0q6372hqrvib7mw21gaq5bq-libxext-1.3.7-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libxext-1.3.7-dev -isystem /nix/store/mvyxqkpyj2mgymljzj9bqi9bmz7ca5fk-xorgproto-2025.1/include -fmacro-prefix-map=/nix/store/mvyxqkpyj2mgymljzj9bqi9bmz7ca5fk-xorgproto-2025.1=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-xorgproto-2025.1 -isystem /nix/store/hd6i8dzybk2jqwqh6frarw30w15yqq9b-libxau-1.0.12-dev/include -fmacro-prefix-map=/nix/store/hd6i8dzybk2jqwqh6frarw30w15yqq9b-libxau-1.0.12-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libxau-1.0.12-dev -isystem /nix/store/94m0129pm3jlbg4fj8py92j1vi870m9c-libxrender-0.9.12-dev/include -fmacro-prefix-map=/nix/store/94m0129pm3jlbg4fj8py92j1vi870m9c-libxrender-0.9.12-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libxrender-0.9.12-dev -isystem /nix/store/4303g76pqhl7r8a2xvci0b4bj47bfbjz-libx11-1.8.13-dev/include -fmacro-prefix-map=/nix/store/4303g76pqhl7r8a2xvci0b4bj47bfbjz-libx11-1.8.13-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libx11-1.8.13-dev -isystem /nix/store/x44m80ahg51pz32dr0j39yzsr7bn7d5v-libxcb-1.17.0-dev/include -fmacro-prefix-map=/nix/store/x44m80ahg51pz32dr0j39yzsr7bn7d5v-libxcb-1.17.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libxcb-1.17.0-dev -isystem /nix/store/kw0yjwbvw6arwgwaa3p8rz46qsgy4626-glib-2.86.3-dev/include -fmacro-prefix-map=/nix/store/kw0yjwbvw6arwgwaa3p8rz46qsgy4626-glib-2.86.3-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-glib-2.86.3-dev -isystem /nix/store/lg8kfrcxy4bcwnlwbfn6x3s48k4aawba-libffi-3.5.2-dev/include -fmacro-prefix-map=/nix/store/lg8kfrcxy4bcwnlwbfn6x3s48k4aawba-libffi-3.5.2-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libffi-3.5.2-dev -isystem /nix/store/ypj27q94ay0ybq9aa14gk0cxjv9d7z4m-gettext-1.0/include -fmacro-prefix-map=/nix/store/ypj27q94ay0ybq9aa14gk0cxjv9d7z4m-gettext-1.0=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-gettext-1.0 -isystem /nix/store/5722rfnbamx35h5df4wlvlqrmvmaan7i-glibc-iconv-2.42/include -fmacro-prefix-map=/nix/store/5722rfnbamx35h5df4wlvlqrmvmaan7i-glibc-iconv-2.42=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-glibc-iconv-2.42 -isystem /nix/store/pbyr7jlx85a0vlx623jqjd18cnccb5vv-lcms2-2.18-dev/include -fmacro-prefix-map=/nix/store/pbyr7jlx85a0vlx623jqjd18cnccb5vv-lcms2-2.18-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-lcms2-2.18-dev -isystem /nix/store/ankisnmp03gzp9m0z4bqy1i2ar23wb48-libtiff-4.7.1-dev/include -fmacro-prefix-map=/nix/store/ankisnmp03gzp9m0z4bqy1i2ar23wb48-libtiff-4.7.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libtiff-4.7.1-dev -isystem /nix/store/7xvb5060qcf36ncp47wz62rl3fsccv1g-curl-8.19.0-dev/include -fmacro-prefix-map=/nix/store/7xvb5060qcf36ncp47wz62rl3fsccv1g-curl-8.19.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-curl-8.19.0-dev -isystem /nix/store/dgdzsx6i729gcp1rrz85zbaacgl86gab-krb5-1.22.1-dev/include -fmacro-prefix-map=/nix/store/dgdzsx6i729gcp1rrz85zbaacgl86gab-krb5-1.22.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-krb5-1.22.1-dev -isystem /nix/store/iaf80mkaj9kfgy3h6hf1xqj7la8acr7y-nghttp2-1.68.1-dev/include -fmacro-prefix-map=/nix/store/iaf80mkaj9kfgy3h6hf1xqj7la8acr7y-nghttp2-1.68.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-nghttp2-1.68.1-dev -isystem /nix/store/d2xhslm8a0b1lk0p4plmyip3i194znhy-nghttp3-1.15.0-dev/include -fmacro-prefix-map=/nix/store/d2xhslm8a0b1lk0p4plmyip3i194znhy-nghttp3-1.15.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-nghttp3-1.15.0-dev -isystem /nix/store/yp754aaxmfqdag95053yax1fdaa4s9ck-ngtcp2-1.22.0-dev/include -fmacro-prefix-map=/nix/store/yp754aaxmfqdag95053yax1fdaa4s9ck-ngtcp2-1.22.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-ngtcp2-1.22.0-dev -isystem /nix/store/j3ypygy4pwwgkdrkxkhnhxqkwx4yw8zq-libidn2-2.3.8-dev/include -fmacro-prefix-map=/nix/store/j3ypygy4pwwgkdrkxkhnhxqkwx4yw8zq-libidn2-2.3.8-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libidn2-2.3.8-dev -isystem /nix/store/dy64cxaygvmjfznysgxk501yds8jij6s-openssl-3.6.1-dev/include -fmacro-prefix-map=/nix/store/dy64cxaygvmjfznysgxk501yds8jij6s-openssl-3.6.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-openssl-3.6.1-dev -isystem /nix/store/ylldnaarbvwkvpn5dasnjjyvvghh6k3r-libpsl-0.21.5-dev/include -fmacro-prefix-map=/nix/store/ylldnaarbvwkvpn5dasnjjyvvghh6k3r-libpsl-0.21.5-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libpsl-0.21.5-dev -isystem /nix/store/5c04s19in4y2ij0zzkh4y9gqys8rwgc4-libssh2-1.11.1-dev/include -fmacro-prefix-map=/nix/store/5c04s19in4y2ij0zzkh4y9gqys8rwgc4-libssh2-1.11.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libssh2-1.11.1-dev -isystem /nix/store/vbqakw4shfcbmdxs6kkp3jmp9k5br94y-zstd-1.5.7-dev/include -fmacro-prefix-map=/nix/store/vbqakw4shfcbmdxs6kkp3jmp9k5br94y-zstd-1.5.7-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-zstd-1.5.7-dev -isystem /nix/store/xafb1qxw69j6fg1s8ln2drppm2zjjfr5-nss-3.112.3-dev/include -fmacro-prefix-map=/nix/store/xafb1qxw69j6fg1s8ln2drppm2zjjfr5-nss-3.112.3-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-nss-3.112.3-dev -isystem /nix/store/3qfr4jp73jac5rnkx8xj58whv4yc80zy-nspr-4.38.2-dev/include -fmacro-prefix-map=/nix/store/3qfr4jp73jac5rnkx8xj58whv4yc80zy-nspr-4.38.2-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-nspr-4.38.2-dev -isystem /nix/store/l7nryi3685lc6di1wbyfmb5q3v3xmfqz-ghostscript-with-X-10.06.0/include -fmacro-prefix-map=/nix/store/l7nryi3685lc6di1wbyfmb5q3v3xmfqz-ghostscript-with-X-10.06.0=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-ghostscript-with-X-10.06.0 -isystem /nix/store/hn59rqwq5j0z7l13yns903l6ibylwz1g-imagemagick-7.1.2-19-dev/include -fmacro-prefix-map=/nix/store/hn59rqwq5j0z7l13yns903l6ibylwz1g-imagemagick-7.1.2-19-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-imagemagick-7.1.2-19-dev -isystem /nix/store/vd0i6w0g7wgj621lpzc2dsld42fsvh6c-libxt-1.3.1-dev/include -fmacro-prefix-map=/nix/store/vd0i6w0g7wgj621lpzc2dsld42fsvh6c-libxt-1.3.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libxt-1.3.1-dev -isystem /nix/store/sl65d0g3k4f6v5w7xclx334zzcj1w533-libsm-1.2.6-dev/include -fmacro-prefix-map=/nix/store/sl65d0g3k4f6v5w7xclx334zzcj1w533-libsm-1.2.6-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libsm-1.2.6-dev -isystem /nix/store/07rdpwd0gxa48k7p7p9mk6h0s0p5zknc-libice-1.1.2-dev/include -fmacro-prefix-map=/nix/store/07rdpwd0gxa48k7p7p9mk6h0s0p5zknc-libice-1.1.2-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libice-1.1.2-dev -isystem /nix/store/vdz5z5d4qvsfqdafihrfwzi5r7wr24lk-libwebp-1.6.0/include -fmacro-prefix-map=/nix/store/vdz5z5d4qvsfqdafihrfwzi5r7wr24lk-libwebp-1.6.0=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-libwebp-1.6.0 -isystem /nix/store/wgz6lg6jd6rq3n7gxgaj8i9qm6f5xlbf-fftw-double-3.3.10-dev/include -fmacro-prefix-map=/nix/store/wgz6lg6jd6rq3n7gxgaj8i9qm6f5xlbf-fftw-double-3.3.10-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-fftw-double-3.3.10-dev -isystem /nix/store/p8x5zv9s9qg3ld8b7jdm03hkpdqybjl9-jq-1.8.1-dev/include -fmacro-prefix-map=/nix/store/p8x5zv9s9qg3ld8b7jdm03hkpdqybjl9-jq-1.8.1-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-jq-1.8.1-dev -isystem /nix/store/9xkb4la9kpnsbrs3kw2cij3wjfbv6j6g-duckdb-1.5.2-dev/include -fmacro-prefix-map=/nix/store/9xkb4la9kpnsbrs3kw2cij3wjfbv6j6g-duckdb-1.5.2-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-duckdb-1.5.2-dev -isystem /nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12/include -fmacro-prefix-map=/nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-python3-3.13.12 -isystem /nix/store/xswd8j43wkqpadsgfl3cnf1hibvwncrw-lld-19.1.7-dev/include -fmacro-prefix-map=/nix/store/xswd8j43wkqpadsgfl3cnf1hibvwncrw-lld-19.1.7-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-lld-19.1.7-dev -isystem /nix/store/x78aqw188hv2nmj8hbbl4q9knhns4qf2-xz-5.8.3-dev/include -fmacro-prefix-map=/nix/store/x78aqw188hv2nmj8hbbl4q9knhns4qf2-xz-5.8.3-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-xz-5.8.3-dev -isystem /nix/store/i7arixgp0p933iicqzfza1dm9g2vgbzf-lz4-1.10.0-dev/include -fmacro-prefix-map=/nix/store/i7arixgp0p933iicqzfza1dm9g2vgbzf-lz4-1.10.0-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-lz4-1.10.0-dev -isystem /nix/store/sw1dgmpi3s1vkjfbdjwj4bliz626fvqp-compiler-rt-libc-19.1.7-dev/include -fmacro-prefix-map=/nix/store/sw1dgmpi3s1vkjfbdjwj4bliz626fvqp-compiler-rt-libc-19.1.7-dev=/nix/store/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-compiler-rt-libc-19.1.7-dev'
export NIX_CFLAGS_COMPILE_FOR_TARGET
NIX_ENFORCE_NO_NATIVE='1'
export NIX_ENFORCE_NO_NATIVE
NIX_HARDENING_ENABLE='bindnow format fortify fortify3 libcxxhardeningfast pic relro stackclashprotection stackprotector strictflexarrays1 strictoverflow zerocallusedregs'
export NIX_HARDENING_ENABLE
NIX_LDFLAGS='-rpath /extra/iohk/claude-env/outputs/out/lib  -L/nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env/lib -L/nix/store/ixhlv41i2wpl84xgjcks061dz4yssbg3-zlib-1.3.2/lib -L/nix/store/2amncb4zvr32gm5d2i8m6gz29c02cn61-bzip2-1.0.8/lib -L/nix/store/7ff90dag7i173s49c5m614wny2lpps1l-brotli-1.2.0-lib/lib -L/nix/store/gsn3vddway3289p6mzy5shd1paly8dp4-libpng-apng-1.6.56/lib -L/nix/store/zr22ggqbv79yv4y4wv06r4grla9h59yx-freetype-2.14.2/lib -L/nix/store/bg6ms0vw071g1fdbx2my6bbzsk62p6vd-fontconfig-2.17.1-lib/lib -L/nix/store/lsln4vpc8spwmb96vjjmg4yd0krd2r7c-libjpeg-turbo-3.1.4/lib -L/nix/store/nrq3pjzsjd4w9vcpgk4a2wfjlqz4xxzw-openjpeg-2.5.4/lib -L/nix/store/hywlq1sf1prbyrhqwf2sbamazp1hghk1-pixman-0.46.4/lib -L/nix/store/2krkc90x3ch0mgkk48fxlglq14nqapdr-libxau-1.0.12/lib -L/nix/store/n1ykqk7ibmp4h5r4x5fng4cn9wjlgj9y-libxext-1.3.7/lib -L/nix/store/5m91jqg1526jzsahrgmd37k4ml3nc5l4-libx11-1.8.13/lib -L/nix/store/dwavjjnzjmp7901n2s61kw40qw8c5rfc-libxrender-0.9.12/lib -L/nix/store/fc1g44pg3i10wfzh3gb4m54pfgclsn76-libxcb-1.17.0/lib -L/nix/store/hyai3q7gvdfppw4ky7s2mvhxvfyp5bh7-libffi-3.5.2/lib -L/nix/store/ypj27q94ay0ybq9aa14gk0cxjv9d7z4m-gettext-1.0/lib -L/nix/store/zcmsivndca5wmam9nwnbjrm0zkgykwfz-glib-2.86.3/lib -L/nix/store/hgvr4xvcqm4a06rq5scgcy6nlk5q89gd-cairo-1.18.4/lib -L/nix/store/3j2yd136zgln9w2hsrvlmazyrhcnfri5-lcms2-2.18/lib -L/nix/store/6w9m0a1v9kx40q341wq4y337s8csqhyn-libtiff-4.7.1/lib -L/nix/store/8cr60j6q7rqmcy4k8l6l1cay9579kd6y-krb5-1.22.1-lib/lib -L/nix/store/hms747x82q23p2g6r6kgzqf7li2ryk39-nghttp2-1.68.1-lib/lib -L/nix/store/133x0z91pizyk8zr4l2ccgqlclpkp1lj-nghttp3-1.15.0/lib -L/nix/store/g5sd94mk8w1a0wiipk81ri0prk136d32-ngtcp2-1.22.0/lib -L/nix/store/sgswwrxkhdlfskklqp4gsbi2cskfg07c-libidn2-2.3.8/lib -L/nix/store/wbyqkb1vpm41s4jb8pv0i9h4jv08xdrv-openssl-3.6.1/lib -L/nix/store/79kr7fafcvvmch13cyczpckz40159pk5-libpsl-0.21.5/lib -L/nix/store/9lzm6krq5ikzbqbmazbh5jmzwph99rz3-libssh2-1.11.1/lib -L/nix/store/k0rqiflg1vkn1kj96br5pfxj40p3srz4-zstd-1.5.7/lib -L/nix/store/pz6b64891m180yb4hadj1jjg3wm3ybng-curl-8.19.0/lib -L/nix/store/amjf7cch3hb5r6l646mwjhrr9384ks4s-nspr-4.38.2/lib -L/nix/store/0wnl2h5xgy1q7bgkqdbiyzxnrq3cmigi-nss-3.112.3/lib -L/nix/store/92ipcswac970qz2iq0nn1yw1jj69xm69-poppler-utils-25.10.0/lib -L/nix/store/l7nryi3685lc6di1wbyfmb5q3v3xmfqz-ghostscript-with-X-10.06.0/lib -L/nix/store/qhw8zihdm481cvia6pd0kl2fmqk9mr2k-libice-1.1.2/lib -L/nix/store/wnmwabsnj34j46c579y0ypc29xjfxjwf-libsm-1.2.6/lib -L/nix/store/vqisl3q8b600dhrpj2a12bk4r5vzn3g4-libxt-1.3.1/lib -L/nix/store/vdz5z5d4qvsfqdafihrfwzi5r7wr24lk-libwebp-1.6.0/lib -L/nix/store/84crpkdlv33nx4kahqzkss83fvpp8x3q-fftw-double-3.3.10/lib -L/nix/store/pjcg9z9zj4hqa7y8jjgsx06rc31q6r8s-imagemagick-7.1.2-19/lib -L/nix/store/09bq2i0kb008ccg3qdbyxv81ggxxnn09-jq-1.8.1/lib -L/nix/store/kqjjmmq70c07hpizbd2sprryrx6a7bs5-duckdb-1.5.2-lib/lib -L/nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12/lib -L/nix/store/477l7v6l11yw7vc1gzmv8ybjl8rs799z-lld-19.1.7-lib/lib -L/nix/store/hmslvsxvs2ijb7iw5krdckai2im6vp2y-xz-5.8.3/lib -L/nix/store/fy28r1ynjk65gnj898k9dabyvzz9mryc-lz4-1.10.0-lib/lib -L/nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env/lib -L/nix/store/ixhlv41i2wpl84xgjcks061dz4yssbg3-zlib-1.3.2/lib -L/nix/store/2amncb4zvr32gm5d2i8m6gz29c02cn61-bzip2-1.0.8/lib -L/nix/store/7ff90dag7i173s49c5m614wny2lpps1l-brotli-1.2.0-lib/lib -L/nix/store/gsn3vddway3289p6mzy5shd1paly8dp4-libpng-apng-1.6.56/lib -L/nix/store/zr22ggqbv79yv4y4wv06r4grla9h59yx-freetype-2.14.2/lib -L/nix/store/bg6ms0vw071g1fdbx2my6bbzsk62p6vd-fontconfig-2.17.1-lib/lib -L/nix/store/lsln4vpc8spwmb96vjjmg4yd0krd2r7c-libjpeg-turbo-3.1.4/lib -L/nix/store/nrq3pjzsjd4w9vcpgk4a2wfjlqz4xxzw-openjpeg-2.5.4/lib -L/nix/store/hywlq1sf1prbyrhqwf2sbamazp1hghk1-pixman-0.46.4/lib -L/nix/store/2krkc90x3ch0mgkk48fxlglq14nqapdr-libxau-1.0.12/lib -L/nix/store/n1ykqk7ibmp4h5r4x5fng4cn9wjlgj9y-libxext-1.3.7/lib -L/nix/store/5m91jqg1526jzsahrgmd37k4ml3nc5l4-libx11-1.8.13/lib -L/nix/store/dwavjjnzjmp7901n2s61kw40qw8c5rfc-libxrender-0.9.12/lib -L/nix/store/fc1g44pg3i10wfzh3gb4m54pfgclsn76-libxcb-1.17.0/lib -L/nix/store/hyai3q7gvdfppw4ky7s2mvhxvfyp5bh7-libffi-3.5.2/lib -L/nix/store/ypj27q94ay0ybq9aa14gk0cxjv9d7z4m-gettext-1.0/lib -L/nix/store/zcmsivndca5wmam9nwnbjrm0zkgykwfz-glib-2.86.3/lib -L/nix/store/hgvr4xvcqm4a06rq5scgcy6nlk5q89gd-cairo-1.18.4/lib -L/nix/store/3j2yd136zgln9w2hsrvlmazyrhcnfri5-lcms2-2.18/lib -L/nix/store/6w9m0a1v9kx40q341wq4y337s8csqhyn-libtiff-4.7.1/lib -L/nix/store/8cr60j6q7rqmcy4k8l6l1cay9579kd6y-krb5-1.22.1-lib/lib -L/nix/store/hms747x82q23p2g6r6kgzqf7li2ryk39-nghttp2-1.68.1-lib/lib -L/nix/store/133x0z91pizyk8zr4l2ccgqlclpkp1lj-nghttp3-1.15.0/lib -L/nix/store/g5sd94mk8w1a0wiipk81ri0prk136d32-ngtcp2-1.22.0/lib -L/nix/store/sgswwrxkhdlfskklqp4gsbi2cskfg07c-libidn2-2.3.8/lib -L/nix/store/wbyqkb1vpm41s4jb8pv0i9h4jv08xdrv-openssl-3.6.1/lib -L/nix/store/79kr7fafcvvmch13cyczpckz40159pk5-libpsl-0.21.5/lib -L/nix/store/9lzm6krq5ikzbqbmazbh5jmzwph99rz3-libssh2-1.11.1/lib -L/nix/store/k0rqiflg1vkn1kj96br5pfxj40p3srz4-zstd-1.5.7/lib -L/nix/store/pz6b64891m180yb4hadj1jjg3wm3ybng-curl-8.19.0/lib -L/nix/store/amjf7cch3hb5r6l646mwjhrr9384ks4s-nspr-4.38.2/lib -L/nix/store/0wnl2h5xgy1q7bgkqdbiyzxnrq3cmigi-nss-3.112.3/lib -L/nix/store/92ipcswac970qz2iq0nn1yw1jj69xm69-poppler-utils-25.10.0/lib -L/nix/store/l7nryi3685lc6di1wbyfmb5q3v3xmfqz-ghostscript-with-X-10.06.0/lib -L/nix/store/qhw8zihdm481cvia6pd0kl2fmqk9mr2k-libice-1.1.2/lib -L/nix/store/wnmwabsnj34j46c579y0ypc29xjfxjwf-libsm-1.2.6/lib -L/nix/store/vqisl3q8b600dhrpj2a12bk4r5vzn3g4-libxt-1.3.1/lib -L/nix/store/vdz5z5d4qvsfqdafihrfwzi5r7wr24lk-libwebp-1.6.0/lib -L/nix/store/84crpkdlv33nx4kahqzkss83fvpp8x3q-fftw-double-3.3.10/lib -L/nix/store/pjcg9z9zj4hqa7y8jjgsx06rc31q6r8s-imagemagick-7.1.2-19/lib -L/nix/store/09bq2i0kb008ccg3qdbyxv81ggxxnn09-jq-1.8.1/lib -L/nix/store/kqjjmmq70c07hpizbd2sprryrx6a7bs5-duckdb-1.5.2-lib/lib -L/nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12/lib -L/nix/store/477l7v6l11yw7vc1gzmv8ybjl8rs799z-lld-19.1.7-lib/lib -L/nix/store/hmslvsxvs2ijb7iw5krdckai2im6vp2y-xz-5.8.3/lib -L/nix/store/fy28r1ynjk65gnj898k9dabyvzz9mryc-lz4-1.10.0-lib/lib'
export NIX_LDFLAGS
NIX_LDFLAGS_FOR_TARGET=' -L/nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env/lib -L/nix/store/ixhlv41i2wpl84xgjcks061dz4yssbg3-zlib-1.3.2/lib -L/nix/store/2amncb4zvr32gm5d2i8m6gz29c02cn61-bzip2-1.0.8/lib -L/nix/store/7ff90dag7i173s49c5m614wny2lpps1l-brotli-1.2.0-lib/lib -L/nix/store/gsn3vddway3289p6mzy5shd1paly8dp4-libpng-apng-1.6.56/lib -L/nix/store/zr22ggqbv79yv4y4wv06r4grla9h59yx-freetype-2.14.2/lib -L/nix/store/bg6ms0vw071g1fdbx2my6bbzsk62p6vd-fontconfig-2.17.1-lib/lib -L/nix/store/lsln4vpc8spwmb96vjjmg4yd0krd2r7c-libjpeg-turbo-3.1.4/lib -L/nix/store/nrq3pjzsjd4w9vcpgk4a2wfjlqz4xxzw-openjpeg-2.5.4/lib -L/nix/store/hywlq1sf1prbyrhqwf2sbamazp1hghk1-pixman-0.46.4/lib -L/nix/store/2krkc90x3ch0mgkk48fxlglq14nqapdr-libxau-1.0.12/lib -L/nix/store/n1ykqk7ibmp4h5r4x5fng4cn9wjlgj9y-libxext-1.3.7/lib -L/nix/store/5m91jqg1526jzsahrgmd37k4ml3nc5l4-libx11-1.8.13/lib -L/nix/store/dwavjjnzjmp7901n2s61kw40qw8c5rfc-libxrender-0.9.12/lib -L/nix/store/fc1g44pg3i10wfzh3gb4m54pfgclsn76-libxcb-1.17.0/lib -L/nix/store/hyai3q7gvdfppw4ky7s2mvhxvfyp5bh7-libffi-3.5.2/lib -L/nix/store/ypj27q94ay0ybq9aa14gk0cxjv9d7z4m-gettext-1.0/lib -L/nix/store/zcmsivndca5wmam9nwnbjrm0zkgykwfz-glib-2.86.3/lib -L/nix/store/hgvr4xvcqm4a06rq5scgcy6nlk5q89gd-cairo-1.18.4/lib -L/nix/store/3j2yd136zgln9w2hsrvlmazyrhcnfri5-lcms2-2.18/lib -L/nix/store/6w9m0a1v9kx40q341wq4y337s8csqhyn-libtiff-4.7.1/lib -L/nix/store/8cr60j6q7rqmcy4k8l6l1cay9579kd6y-krb5-1.22.1-lib/lib -L/nix/store/hms747x82q23p2g6r6kgzqf7li2ryk39-nghttp2-1.68.1-lib/lib -L/nix/store/133x0z91pizyk8zr4l2ccgqlclpkp1lj-nghttp3-1.15.0/lib -L/nix/store/g5sd94mk8w1a0wiipk81ri0prk136d32-ngtcp2-1.22.0/lib -L/nix/store/sgswwrxkhdlfskklqp4gsbi2cskfg07c-libidn2-2.3.8/lib -L/nix/store/wbyqkb1vpm41s4jb8pv0i9h4jv08xdrv-openssl-3.6.1/lib -L/nix/store/79kr7fafcvvmch13cyczpckz40159pk5-libpsl-0.21.5/lib -L/nix/store/9lzm6krq5ikzbqbmazbh5jmzwph99rz3-libssh2-1.11.1/lib -L/nix/store/k0rqiflg1vkn1kj96br5pfxj40p3srz4-zstd-1.5.7/lib -L/nix/store/pz6b64891m180yb4hadj1jjg3wm3ybng-curl-8.19.0/lib -L/nix/store/amjf7cch3hb5r6l646mwjhrr9384ks4s-nspr-4.38.2/lib -L/nix/store/0wnl2h5xgy1q7bgkqdbiyzxnrq3cmigi-nss-3.112.3/lib -L/nix/store/92ipcswac970qz2iq0nn1yw1jj69xm69-poppler-utils-25.10.0/lib -L/nix/store/l7nryi3685lc6di1wbyfmb5q3v3xmfqz-ghostscript-with-X-10.06.0/lib -L/nix/store/qhw8zihdm481cvia6pd0kl2fmqk9mr2k-libice-1.1.2/lib -L/nix/store/wnmwabsnj34j46c579y0ypc29xjfxjwf-libsm-1.2.6/lib -L/nix/store/vqisl3q8b600dhrpj2a12bk4r5vzn3g4-libxt-1.3.1/lib -L/nix/store/vdz5z5d4qvsfqdafihrfwzi5r7wr24lk-libwebp-1.6.0/lib -L/nix/store/84crpkdlv33nx4kahqzkss83fvpp8x3q-fftw-double-3.3.10/lib -L/nix/store/pjcg9z9zj4hqa7y8jjgsx06rc31q6r8s-imagemagick-7.1.2-19/lib -L/nix/store/09bq2i0kb008ccg3qdbyxv81ggxxnn09-jq-1.8.1/lib -L/nix/store/kqjjmmq70c07hpizbd2sprryrx6a7bs5-duckdb-1.5.2-lib/lib -L/nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12/lib -L/nix/store/477l7v6l11yw7vc1gzmv8ybjl8rs799z-lld-19.1.7-lib/lib -L/nix/store/hmslvsxvs2ijb7iw5krdckai2im6vp2y-xz-5.8.3/lib -L/nix/store/fy28r1ynjk65gnj898k9dabyvzz9mryc-lz4-1.10.0-lib/lib'
export NIX_LDFLAGS_FOR_TARGET
NIX_NO_SELF_RPATH='1'
NIX_PKG_CONFIG_WRAPPER_TARGET_TARGET_x86_64_unknown_linux_gnu='1'
export NIX_PKG_CONFIG_WRAPPER_TARGET_TARGET_x86_64_unknown_linux_gnu
NIX_STORE='/nix/store'
export NIX_STORE
NM='nm'
export NM
NM_FOR_TARGET='nm'
export NM_FOR_TARGET
OBJCOPY='objcopy'
export OBJCOPY
OBJCOPY_FOR_TARGET='objcopy'
export OBJCOPY_FOR_TARGET
OBJDUMP='objdump'
export OBJDUMP
OBJDUMP_FOR_TARGET='objdump'
export OBJDUMP_FOR_TARGET
OLDPWD=''
export OLDPWD
OPTERR='1'
OSTYPE='linux-gnu'
PATH='/nix/store/66lksljlljdd5ppgvfk8g89y8xgqcxd7-patchelf-0.15.2/bin:/nix/store/qd70v8g0561vm8m33kmnp79z00cgyi5n-gcc-wrapper-15.2.0/bin:/nix/store/sanx9fg8mry8mq92zhlm5qvb83qlxrlx-gcc-15.2.0/bin:/nix/store/pf30k3mg7n6bibc1k6609gyq7glk00k2-glibc-2.42-61-bin/bin:/nix/store/jjxngswsb214vb58qx485jhmilf0kxxy-coreutils-9.10/bin:/nix/store/kfwagnh6i1mysf7vxq679rzh30z9zj3g-binutils-wrapper-2.46/bin:/nix/store/p2vkw5s89ff1fs2d2rxqxiqil9s0jpcm-binutils-2.46/bin:/nix/store/785jidgnryzj566s25s3rb262d4g5znb-nodejs-24.14.1/bin:/nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env/bin:/nix/store/cifzx7qr3mpcphz1bnlww4llshrvczyg-pandoc-cli-3.7.0.2/bin:/nix/store/0rn2xh3zciwdr8sjg79ir79dbr6lnmfb-gnumake-4.4.1/bin:/nix/store/04ys3zgcil28yj4afyk6p3dlrfv60s1h-time-1.10/bin:/nix/store/r7bp82svf04jqw3x7wnjlyr951jkf85k-freetype-2.14.2-dev/bin:/nix/store/zj6r42syyswkhrr174bzppj3n7xhq936-bzip2-1.0.8-bin/bin:/nix/store/mj1k1nsdqr0mp9wsnkg7blgh3xf5wssv-brotli-1.2.0/bin:/nix/store/h176f4dhbcpj4lpf8sn28vdqp1mks5jk-libpng-apng-1.6.56-dev/bin:/nix/store/v18drszzvspk1wlq06r68nxgpn2b4cvd-fontconfig-2.17.1-bin/bin:/nix/store/v70k3ch8rcw9b0la3axqb34dkyxqnx2s-libjpeg-turbo-3.1.4-bin/bin:/nix/store/nrq3pjzsjd4w9vcpgk4a2wfjlqz4xxzw-openjpeg-2.5.4/bin:/nix/store/8zhjvm4vixgvg089nn4wv7hhxlp7qg2c-cairo-1.18.4-dev/bin:/nix/store/kw0yjwbvw6arwgwaa3p8rz46qsgy4626-glib-2.86.3-dev/bin:/nix/store/ypj27q94ay0ybq9aa14gk0cxjv9d7z4m-gettext-1.0/bin:/nix/store/b9jcqjd8gnxr87p7wc91lmbyd90kzlc1-glib-2.86.3-bin/bin:/nix/store/xiq38z94b68c8dgj7nfx9xlh2984c2mp-lcms2-2.18-bin/bin:/nix/store/cbdy1d44cqa9j7x0ga72dqsk4p49ih70-libtiff-4.7.1-bin/bin:/nix/store/7xvb5060qcf36ncp47wz62rl3fsccv1g-curl-8.19.0-dev/bin:/nix/store/dgdzsx6i729gcp1rrz85zbaacgl86gab-krb5-1.22.1-dev/bin:/nix/store/qp2qzmh67rqy6i36sh3iqznk1akiw4q1-krb5-1.22.1/bin:/nix/store/yvxyaqh3bzj7nr64zlr1axyf76fgcszb-nghttp2-1.68.1/bin:/nix/store/a327a5lqzwakcs3yjgx4sa1931fph5gf-libidn2-2.3.8-bin/bin:/nix/store/2di90l89y2ygdy3rbws7dhg9nrvd3pnx-openssl-3.6.1-bin/bin:/nix/store/79kr7fafcvvmch13cyczpckz40159pk5-libpsl-0.21.5/bin:/nix/store/91jddg4g6788ilnk3kww8j8jhxhzk6d3-zstd-1.5.7-bin/bin:/nix/store/k0rqiflg1vkn1kj96br5pfxj40p3srz4-zstd-1.5.7/bin:/nix/store/sm2nq18jjqp4x0sxpl6lrvwl9rx6mvj2-curl-8.19.0-bin/bin:/nix/store/xafb1qxw69j6fg1s8ln2drppm2zjjfr5-nss-3.112.3-dev/bin:/nix/store/3qfr4jp73jac5rnkx8xj58whv4yc80zy-nspr-4.38.2-dev/bin:/nix/store/92ipcswac970qz2iq0nn1yw1jj69xm69-poppler-utils-25.10.0/bin:/nix/store/l7nryi3685lc6di1wbyfmb5q3v3xmfqz-ghostscript-with-X-10.06.0/bin:/nix/store/hn59rqwq5j0z7l13yns903l6ibylwz1g-imagemagick-7.1.2-19-dev/bin:/nix/store/vdz5z5d4qvsfqdafihrfwzi5r7wr24lk-libwebp-1.6.0/bin:/nix/store/wgz6lg6jd6rq3n7gxgaj8i9qm6f5xlbf-fftw-double-3.3.10-dev/bin:/nix/store/pjcg9z9zj4hqa7y8jjgsx06rc31q6r8s-imagemagick-7.1.2-19/bin:/nix/store/v5c3inhfq6xshmwg1c254vfbcy4jp3k9-jq-1.8.1-bin/bin:/nix/store/n4h91v3p9v5hfgcrmfashil26nsrsrhs-duckdb-1.5.2/bin:/nix/store/jx6bzribg9fa0mxbr8b602rq74k24dr7-python3.13-yamllint-1.37.1/bin:/nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12/bin:/nix/store/7xiiq153kv13wcqb6j5zffz2g778nssv-shellcheck-0.11.0-bin/bin:/nix/store/hn7cpgmj18mx8lj5wsnjgcy158cnfyz1-statix-0.5.8/bin:/nix/store/ivy6wb23x19x29qz49y98amkch1jbz84-elan-4.2.1/bin:/nix/store/xiy3ydpzw5bdqqd7ri8qbg3bn4r2qxg1-rustup-1.29.0/bin:/nix/store/biagcw4fwc90ala8pxbdb919khj39rzy-clang-wrapper-19.1.7/bin:/nix/store/8xnhbkhlxvg9b4703lds4mirmipws2gf-clang-19.1.7/bin:/nix/store/vr4sjc5ajni6j76wqkvkx84q141270ak-binutils-wrapper-2.46/bin:/nix/store/hvihdgv65b31lrw3rdybjz1m8q314qyi-lld-19.1.7/bin:/nix/store/v2i1hgv567g3v91im5x4g5bff52143i0-cmake-4.1.2/bin:/nix/store/v7mjkia7ki79s5i24ldbzq1khalhgzk0-pkg-config-wrapper-0.29.2/bin:/nix/store/fszv4kq85ywrpq6dy2wydl1ggkbc6sjp-emscripten-5.0.6/bin:/nix/store/pxhpmfr4qwihzxqam9642a9r7jpvbblr-typescript-5.9.3/bin:/nix/store/246dw7jxjgznw9fql388hj43yyknlqmn-vscode-1.116.0/bin:/nix/store/9lhr1c3l9qzv8pzp3idmii1nwvxxjys3-gzip-1.14/bin:/nix/store/2nm5c858fh52s6mhcffm07s3biaxys44-xz-5.8.3-bin/bin:/nix/store/m7m89ms25namgzbhcx6nf42jgjx55lcx-lz4-1.10.0/bin:/nix/store/qpf8bnaad0j8g4ggl65hvfs8l5y1alwp-mermaid-cli-11.12.0/bin:/nix/store/nkai8ssk915yc9mvj0xi28zliwwsaacp-zpaq-7.15/bin:/nix/store/0l71d5r282xjml5zhd3knf4syinczqwh-R-4.5.3-wrapper/bin:/nix/store/9agl8i5ax5w0x01rsgazhizhgpshb8pg-compiler-rt-libc-19.1.7/bin:/nix/store/jjxngswsb214vb58qx485jhmilf0kxxy-coreutils-9.10/bin:/nix/store/vhsirn9m1ifmnw5g1qczzhvqkx6lw1if-findutils-4.10.0/bin:/nix/store/hx084k7pgz4n0vgkvil9gbcnl8y6p1xf-diffutils-3.12/bin:/nix/store/af4a8i43kc2ss4rnmf0swkk2mprsw6xq-gnused-4.9/bin:/nix/store/wf7lr2hf43546jc5kwqh3dbxnpcnw1mn-gnugrep-3.12/bin:/nix/store/lakv43kv98sl6h0ba6wnyg513mcq61vl-gawk-5.4.0/bin:/nix/store/rnvb7bvp53v2dw7pcwh9xb89x5z4rjib-gnutar-1.35/bin:/nix/store/9lhr1c3l9qzv8pzp3idmii1nwvxxjys3-gzip-1.14/bin:/nix/store/zj6r42syyswkhrr174bzppj3n7xhq936-bzip2-1.0.8-bin/bin:/nix/store/yvrwcs1a45rj8142n0l2w9q9s6akamjr-gnumake-4.4.1/bin:/nix/store/i27rhb3nr65rkrwz36bchkwmav6ggsmn-bash-5.3p9/bin:/nix/store/zj7mxwji29zvj9vl70iip7gw4h6ljfam-patch-2.8/bin:/nix/store/2nm5c858fh52s6mhcffm07s3biaxys44-xz-5.8.3-bin/bin:/nix/store/iscmg3ivhx7z67dz14lrg7p77gnsa4dw-file-5.45/bin'
export PATH
PKG_CONFIG_FOR_TARGET='pkg-config'
export PKG_CONFIG_FOR_TARGET
PKG_CONFIG_PATH_FOR_TARGET='/nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env/lib/pkgconfig:/nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env/share/pkgconfig:/nix/store/rhp41khpds0m218gdp4lagkhb957mi42-poppler-utils-25.10.0-dev/lib/pkgconfig:/nix/store/3yl2s5r3yph88imzbgbdrh8pbs9rcjcs-zlib-1.3.2-dev/share/pkgconfig:/nix/store/r7bp82svf04jqw3x7wnjlyr951jkf85k-freetype-2.14.2-dev/lib/pkgconfig:/nix/store/bh64ycxf96cc4v43m77nszmpvbs0pfv7-bzip2-1.0.8-dev/lib/pkgconfig:/nix/store/1x1msj33z37b65vlxbs51l7i4j92qn9h-brotli-1.2.0-dev/lib/pkgconfig:/nix/store/h176f4dhbcpj4lpf8sn28vdqp1mks5jk-libpng-apng-1.6.56-dev/lib/pkgconfig:/nix/store/gjg4aagfcn6r96c73rz4rwbclbdqqc6v-fontconfig-2.17.1-dev/lib/pkgconfig:/nix/store/b63lk3n7piwf7a790c4cy0zinqi184fs-libjpeg-turbo-3.1.4-dev/lib/pkgconfig:/nix/store/5q46i43k18sspv8wjpasmrgl5n8y7j1s-openjpeg-2.5.4-dev/lib/pkgconfig:/nix/store/8zhjvm4vixgvg089nn4wv7hhxlp7qg2c-cairo-1.18.4-dev/lib/pkgconfig:/nix/store/hywlq1sf1prbyrhqwf2sbamazp1hghk1-pixman-0.46.4/lib/pkgconfig:/nix/store/1kx6y7spy0q6372hqrvib7mw21gaq5bq-libxext-1.3.7-dev/lib/pkgconfig:/nix/store/mvyxqkpyj2mgymljzj9bqi9bmz7ca5fk-xorgproto-2025.1/share/pkgconfig:/nix/store/hd6i8dzybk2jqwqh6frarw30w15yqq9b-libxau-1.0.12-dev/lib/pkgconfig:/nix/store/94m0129pm3jlbg4fj8py92j1vi870m9c-libxrender-0.9.12-dev/lib/pkgconfig:/nix/store/4303g76pqhl7r8a2xvci0b4bj47bfbjz-libx11-1.8.13-dev/lib/pkgconfig:/nix/store/x44m80ahg51pz32dr0j39yzsr7bn7d5v-libxcb-1.17.0-dev/lib/pkgconfig:/nix/store/kw0yjwbvw6arwgwaa3p8rz46qsgy4626-glib-2.86.3-dev/lib/pkgconfig:/nix/store/lg8kfrcxy4bcwnlwbfn6x3s48k4aawba-libffi-3.5.2-dev/lib/pkgconfig:/nix/store/pbyr7jlx85a0vlx623jqjd18cnccb5vv-lcms2-2.18-dev/lib/pkgconfig:/nix/store/ankisnmp03gzp9m0z4bqy1i2ar23wb48-libtiff-4.7.1-dev/lib/pkgconfig:/nix/store/7xvb5060qcf36ncp47wz62rl3fsccv1g-curl-8.19.0-dev/lib/pkgconfig:/nix/store/dgdzsx6i729gcp1rrz85zbaacgl86gab-krb5-1.22.1-dev/lib/pkgconfig:/nix/store/iaf80mkaj9kfgy3h6hf1xqj7la8acr7y-nghttp2-1.68.1-dev/lib/pkgconfig:/nix/store/d2xhslm8a0b1lk0p4plmyip3i194znhy-nghttp3-1.15.0-dev/lib/pkgconfig:/nix/store/yp754aaxmfqdag95053yax1fdaa4s9ck-ngtcp2-1.22.0-dev/lib/pkgconfig:/nix/store/j3ypygy4pwwgkdrkxkhnhxqkwx4yw8zq-libidn2-2.3.8-dev/lib/pkgconfig:/nix/store/dy64cxaygvmjfznysgxk501yds8jij6s-openssl-3.6.1-dev/lib/pkgconfig:/nix/store/ylldnaarbvwkvpn5dasnjjyvvghh6k3r-libpsl-0.21.5-dev/lib/pkgconfig:/nix/store/5c04s19in4y2ij0zzkh4y9gqys8rwgc4-libssh2-1.11.1-dev/lib/pkgconfig:/nix/store/vbqakw4shfcbmdxs6kkp3jmp9k5br94y-zstd-1.5.7-dev/lib/pkgconfig:/nix/store/xafb1qxw69j6fg1s8ln2drppm2zjjfr5-nss-3.112.3-dev/lib/pkgconfig:/nix/store/3qfr4jp73jac5rnkx8xj58whv4yc80zy-nspr-4.38.2-dev/lib/pkgconfig:/nix/store/hn59rqwq5j0z7l13yns903l6ibylwz1g-imagemagick-7.1.2-19-dev/lib/pkgconfig:/nix/store/vd0i6w0g7wgj621lpzc2dsld42fsvh6c-libxt-1.3.1-dev/lib/pkgconfig:/nix/store/sl65d0g3k4f6v5w7xclx334zzcj1w533-libsm-1.2.6-dev/lib/pkgconfig:/nix/store/07rdpwd0gxa48k7p7p9mk6h0s0p5zknc-libice-1.1.2-dev/lib/pkgconfig:/nix/store/vdz5z5d4qvsfqdafihrfwzi5r7wr24lk-libwebp-1.6.0/lib/pkgconfig:/nix/store/wgz6lg6jd6rq3n7gxgaj8i9qm6f5xlbf-fftw-double-3.3.10-dev/lib/pkgconfig:/nix/store/p8x5zv9s9qg3ld8b7jdm03hkpdqybjl9-jq-1.8.1-dev/lib/pkgconfig:/nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12/lib/pkgconfig:/nix/store/x78aqw188hv2nmj8hbbl4q9knhns4qf2-xz-5.8.3-dev/lib/pkgconfig:/nix/store/i7arixgp0p933iicqzfza1dm9g2vgbzf-lz4-1.10.0-dev/lib/pkgconfig:/nix/store/0l71d5r282xjml5zhd3knf4syinczqwh-R-4.5.3-wrapper/lib/pkgconfig'
export PKG_CONFIG_PATH_FOR_TARGET
PS4='+ '
PYTHONHASHSEED='0'
export PYTHONHASHSEED
PYTHONNOUSERSITE='1'
export PYTHONNOUSERSITE
PYTHONPATH='/nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env/lib/python3.13/site-packages:/nix/store/jx6bzribg9fa0mxbr8b602rq74k24dr7-python3.13-yamllint-1.37.1/lib/python3.13/site-packages:/nix/store/jl0mxihyizv77l66mzbvmv49iiri72sd-python3.13-pyyaml-6.0.3/lib/python3.13/site-packages:/nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12/lib/python3.13/site-packages:/nix/store/pdjdz9mqsj6az0znlrgh2fj6wp1rb032-python3.13-pathspec-0.12.1/lib/python3.13/site-packages'
export PYTHONPATH
RANLIB='ranlib'
export RANLIB
RANLIB_FOR_TARGET='ranlib'
export RANLIB_FOR_TARGET
READELF='readelf'
export READELF
READELF_FOR_TARGET='readelf'
export READELF_FOR_TARGET
SHELL='/nix/store/i27rhb3nr65rkrwz36bchkwmav6ggsmn-bash-5.3p9/bin/bash'
export SHELL
SIZE='size'
export SIZE
SIZE_FOR_TARGET='size'
export SIZE_FOR_TARGET
SOURCE_DATE_EPOCH='315532800'
export SOURCE_DATE_EPOCH
STRINGS='strings'
export STRINGS
STRINGS_FOR_TARGET='strings'
export STRINGS_FOR_TARGET
STRIP='strip'
export STRIP
STRIP_FOR_TARGET='strip'
export STRIP_FOR_TARGET
XDG_DATA_DIRS='/nix/store/66lksljlljdd5ppgvfk8g89y8xgqcxd7-patchelf-0.15.2/share'
export XDG_DATA_DIRS
_PYTHON_HOST_PLATFORM='linux-x86_64'
export _PYTHON_HOST_PLATFORM
_PYTHON_SYSCONFIGDATA_NAME='_sysconfigdata__linux_x86_64-linux-gnu'
export _PYTHON_SYSCONFIGDATA_NAME
__structuredAttrs=''
export __structuredAttrs
_substituteStream_has_warned_replace_deprecation='false'
buildInputs='/nix/store/785jidgnryzj566s25s3rb262d4g5znb-nodejs-24.14.1 /nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env /nix/store/cifzx7qr3mpcphz1bnlww4llshrvczyg-pandoc-cli-3.7.0.2 /nix/store/0rn2xh3zciwdr8sjg79ir79dbr6lnmfb-gnumake-4.4.1 /nix/store/04ys3zgcil28yj4afyk6p3dlrfv60s1h-time-1.10 /nix/store/rhp41khpds0m218gdp4lagkhb957mi42-poppler-utils-25.10.0-dev /nix/store/l7nryi3685lc6di1wbyfmb5q3v3xmfqz-ghostscript-with-X-10.06.0 /nix/store/hn59rqwq5j0z7l13yns903l6ibylwz1g-imagemagick-7.1.2-19-dev /nix/store/p8x5zv9s9qg3ld8b7jdm03hkpdqybjl9-jq-1.8.1-dev /nix/store/9xkb4la9kpnsbrs3kw2cij3wjfbv6j6g-duckdb-1.5.2-dev /nix/store/7xvb5060qcf36ncp47wz62rl3fsccv1g-curl-8.19.0-dev /nix/store/jx6bzribg9fa0mxbr8b602rq74k24dr7-python3.13-yamllint-1.37.1 /nix/store/09hk83dw55dpbw1f8km58pycmbfr186k-shellcheck-0.11.0 /nix/store/hn7cpgmj18mx8lj5wsnjgcy158cnfyz1-statix-0.5.8 /nix/store/ivy6wb23x19x29qz49y98amkch1jbz84-elan-4.2.1 /nix/store/xiy3ydpzw5bdqqd7ri8qbg3bn4r2qxg1-rustup-1.29.0 /nix/store/biagcw4fwc90ala8pxbdb919khj39rzy-clang-wrapper-19.1.7 /nix/store/xswd8j43wkqpadsgfl3cnf1hibvwncrw-lld-19.1.7-dev /nix/store/v2i1hgv567g3v91im5x4g5bff52143i0-cmake-4.1.2 /nix/store/v7mjkia7ki79s5i24ldbzq1khalhgzk0-pkg-config-wrapper-0.29.2 /nix/store/dy64cxaygvmjfznysgxk501yds8jij6s-openssl-3.6.1-dev /nix/store/fszv4kq85ywrpq6dy2wydl1ggkbc6sjp-emscripten-5.0.6 /nix/store/pxhpmfr4qwihzxqam9642a9r7jpvbblr-typescript-5.9.3 /nix/store/246dw7jxjgznw9fql388hj43yyknlqmn-vscode-1.116.0 /nix/store/9lhr1c3l9qzv8pzp3idmii1nwvxxjys3-gzip-1.14 /nix/store/bh64ycxf96cc4v43m77nszmpvbs0pfv7-bzip2-1.0.8-dev /nix/store/x78aqw188hv2nmj8hbbl4q9knhns4qf2-xz-5.8.3-dev /nix/store/vbqakw4shfcbmdxs6kkp3jmp9k5br94y-zstd-1.5.7-dev /nix/store/i7arixgp0p933iicqzfza1dm9g2vgbzf-lz4-1.10.0-dev /nix/store/1x1msj33z37b65vlxbs51l7i4j92qn9h-brotli-1.2.0-dev /nix/store/qpf8bnaad0j8g4ggl65hvfs8l5y1alwp-mermaid-cli-11.12.0 /nix/store/nkai8ssk915yc9mvj0xi28zliwwsaacp-zpaq-7.15 /nix/store/0l71d5r282xjml5zhd3knf4syinczqwh-R-4.5.3-wrapper'
export buildInputs
buildPhase='{ echo "------------------------------------------------------------";
  echo " WARNING: the existence of this path is not guaranteed.";
  echo " It is an internal implementation detail for pkgs.mkShell.";
  echo "------------------------------------------------------------";
  echo;
  # Record all build inputs as runtime dependencies
  export;
} >> "$out"
'
export buildPhase
builder='/nix/store/i27rhb3nr65rkrwz36bchkwmav6ggsmn-bash-5.3p9/bin/bash'
export builder
cmakeFlags=''
export cmakeFlags
configureFlags=''
export configureFlags
configurePhase='cmakeConfigurePhase'
defaultBuildInputs=''
defaultNativeBuildInputs='/nix/store/66lksljlljdd5ppgvfk8g89y8xgqcxd7-patchelf-0.15.2 /nix/store/9vv51km72lpngs6aixxplrr3c88q4c3c-update-autotools-gnu-config-scripts-hook /nix/store/0y5xmdb7qfvimjwbq7ibg1xdgkgjwqng-no-broken-symlinks.sh /nix/store/cv1d7p48379km6a85h4zp6kr86brh32q-audit-tmpdir.sh /nix/store/85clx3b0xkdf58jn161iy80y5223ilbi-compress-man-pages.sh /nix/store/p3l1a5y7nllfyrjn2krlwgcc3z0cd3fq-make-symlinks-relative.sh /nix/store/5yzw0vhkyszf2d179m0qfkgxmp5wjjx4-move-docs.sh /nix/store/fyaryjvghbkpfnsyw97hb3lyb37s1pd6-move-lib64.sh /nix/store/kd4xwxjpjxi71jkm6ka0np72if9rm3y0-move-sbin.sh /nix/store/pag6l61paj1dc9sv15l7bm5c17xn5kyk-move-systemd-user-units.sh /nix/store/cmzya9irvxzlkh7lfy6i82gbp0saxqj3-multiple-outputs.sh /nix/store/x8c40nfigps493a07sdr2pm5s9j1cdc0-patch-shebangs.sh /nix/store/cickvswrvann041nqxb0rxilc46svw1n-prune-libtool-files.sh /nix/store/xyff06pkhki3qy1ls77w10s0v79c9il0-reproducible-builds.sh /nix/store/z7k98578dfzi6l3hsvbivzm7hfqlk0zc-set-source-date-epoch-to-latest.sh /nix/store/pilsssjjdxvdphlg2h19p0bfx5q0jzkn-strip.sh /nix/store/qd70v8g0561vm8m33kmnp79z00cgyi5n-gcc-wrapper-15.2.0'
depsBuildBuild=''
export depsBuildBuild
depsBuildBuildPropagated=''
export depsBuildBuildPropagated
depsBuildTarget=''
export depsBuildTarget
depsBuildTargetPropagated=''
export depsBuildTargetPropagated
depsHostHost=''
export depsHostHost
depsHostHostPropagated=''
export depsHostHostPropagated
depsTargetTarget=''
export depsTargetTarget
depsTargetTargetPropagated=''
export depsTargetTargetPropagated
doCheck=''
export doCheck
doInstallCheck=''
export doInstallCheck
dontAddDisableDepTrack='1'
export dontAddDisableDepTrack
declare -a envBuildBuildHooks=()
declare -a envBuildHostHooks=()
declare -a envBuildTargetHooks=()
declare -a envHostHostHooks=('ccWrapper_addCVars' 'bintoolsWrapper_addLDVars' 'gettextDataDirsHook' 'addPythonPath' 'sysconfigdataHook' )
declare -a envHostTargetHooks=('ccWrapper_addCVars' 'bintoolsWrapper_addLDVars' 'gettextDataDirsHook' 'addPythonPath' 'sysconfigdataHook' )
declare -a envTargetTargetHooks=('make_glib_find_gsettings_schemas' 'ccWrapper_addCVars' 'bintoolsWrapper_addLDVars' 'addCMakeParams' 'pkgConfigWrapper_addPkgConfigPath' 'addRLibPath' )
declare -a fixupOutputHooks=('if [ -z "${dontPatchELF-}" ]; then patchELF "$prefix"; fi' 'if [[ -z "${noAuditTmpdir-}" && -e "$prefix" ]]; then auditTmpdir "$prefix"; fi' 'if [ -z "${dontGzipMan-}" ]; then compressManPages "$prefix"; fi' '_moveLib64' '_moveSbin' '_moveSystemdUserUnits' 'patchShebangsAuto' '_pruneLibtoolFiles' '_doStrip' )
flag='-L/nix/store/fy28r1ynjk65gnj898k9dabyvzz9mryc-lz4-1.10.0-lib/lib'
iframework_seen=''
initialPath='/nix/store/jjxngswsb214vb58qx485jhmilf0kxxy-coreutils-9.10 /nix/store/vhsirn9m1ifmnw5g1qczzhvqkx6lw1if-findutils-4.10.0 /nix/store/hx084k7pgz4n0vgkvil9gbcnl8y6p1xf-diffutils-3.12 /nix/store/af4a8i43kc2ss4rnmf0swkk2mprsw6xq-gnused-4.9 /nix/store/wf7lr2hf43546jc5kwqh3dbxnpcnw1mn-gnugrep-3.12 /nix/store/lakv43kv98sl6h0ba6wnyg513mcq61vl-gawk-5.4.0 /nix/store/rnvb7bvp53v2dw7pcwh9xb89x5z4rjib-gnutar-1.35 /nix/store/9lhr1c3l9qzv8pzp3idmii1nwvxxjys3-gzip-1.14 /nix/store/zj6r42syyswkhrr174bzppj3n7xhq936-bzip2-1.0.8-bin /nix/store/yvrwcs1a45rj8142n0l2w9q9s6akamjr-gnumake-4.4.1 /nix/store/i27rhb3nr65rkrwz36bchkwmav6ggsmn-bash-5.3p9 /nix/store/zj7mxwji29zvj9vl70iip7gw4h6ljfam-patch-2.8 /nix/store/2nm5c858fh52s6mhcffm07s3biaxys44-xz-5.8.3-bin /nix/store/iscmg3ivhx7z67dz14lrg7p77gnsa4dw-file-5.45'
isystem_seen=''
mesonFlags=''
export mesonFlags
name='nix-shell-env'
export name
nativeBuildInputs=''
export nativeBuildInputs
out='/extra/iohk/claude-env/outputs/out'
export out
outputBin='out'
outputDev='out'
outputDevdoc='REMOVE'
outputDevman='out'
outputDoc='out'
outputInclude='out'
outputInfo='out'
outputLib='out'
outputMan='out'
outputs='out'
export outputs
patches=''
export patches
phases='buildPhase'
export phases
pkg='/nix/store/qd70v8g0561vm8m33kmnp79z00cgyi5n-gcc-wrapper-15.2.0'
declare -a pkgsBuildBuild=()
declare -a pkgsBuildHost=('/nix/store/66lksljlljdd5ppgvfk8g89y8xgqcxd7-patchelf-0.15.2' '/nix/store/9vv51km72lpngs6aixxplrr3c88q4c3c-update-autotools-gnu-config-scripts-hook' '/nix/store/0y5xmdb7qfvimjwbq7ibg1xdgkgjwqng-no-broken-symlinks.sh' '/nix/store/cv1d7p48379km6a85h4zp6kr86brh32q-audit-tmpdir.sh' '/nix/store/85clx3b0xkdf58jn161iy80y5223ilbi-compress-man-pages.sh' '/nix/store/p3l1a5y7nllfyrjn2krlwgcc3z0cd3fq-make-symlinks-relative.sh' '/nix/store/5yzw0vhkyszf2d179m0qfkgxmp5wjjx4-move-docs.sh' '/nix/store/fyaryjvghbkpfnsyw97hb3lyb37s1pd6-move-lib64.sh' '/nix/store/kd4xwxjpjxi71jkm6ka0np72if9rm3y0-move-sbin.sh' '/nix/store/pag6l61paj1dc9sv15l7bm5c17xn5kyk-move-systemd-user-units.sh' '/nix/store/cmzya9irvxzlkh7lfy6i82gbp0saxqj3-multiple-outputs.sh' '/nix/store/x8c40nfigps493a07sdr2pm5s9j1cdc0-patch-shebangs.sh' '/nix/store/cickvswrvann041nqxb0rxilc46svw1n-prune-libtool-files.sh' '/nix/store/xyff06pkhki3qy1ls77w10s0v79c9il0-reproducible-builds.sh' '/nix/store/z7k98578dfzi6l3hsvbivzm7hfqlk0zc-set-source-date-epoch-to-latest.sh' '/nix/store/pilsssjjdxvdphlg2h19p0bfx5q0jzkn-strip.sh' '/nix/store/qd70v8g0561vm8m33kmnp79z00cgyi5n-gcc-wrapper-15.2.0' '/nix/store/kfwagnh6i1mysf7vxq679rzh30z9zj3g-binutils-wrapper-2.46' )
declare -a pkgsBuildTarget=()
declare -a pkgsHostHost=()
declare -a pkgsHostTarget=('/nix/store/785jidgnryzj566s25s3rb262d4g5znb-nodejs-24.14.1' '/nix/store/mp0qkwiyr14zf3gpkpln1dnv00br7cpr-python3-3.13.12-env' '/nix/store/cifzx7qr3mpcphz1bnlww4llshrvczyg-pandoc-cli-3.7.0.2' '/nix/store/0rn2xh3zciwdr8sjg79ir79dbr6lnmfb-gnumake-4.4.1' '/nix/store/04ys3zgcil28yj4afyk6p3dlrfv60s1h-time-1.10' '/nix/store/rhp41khpds0m218gdp4lagkhb957mi42-poppler-utils-25.10.0-dev' '/nix/store/3yl2s5r3yph88imzbgbdrh8pbs9rcjcs-zlib-1.3.2-dev' '/nix/store/ixhlv41i2wpl84xgjcks061dz4yssbg3-zlib-1.3.2' '/nix/store/r7bp82svf04jqw3x7wnjlyr951jkf85k-freetype-2.14.2-dev' '/nix/store/bh64ycxf96cc4v43m77nszmpvbs0pfv7-bzip2-1.0.8-dev' '/nix/store/zj6r42syyswkhrr174bzppj3n7xhq936-bzip2-1.0.8-bin' '/nix/store/2amncb4zvr32gm5d2i8m6gz29c02cn61-bzip2-1.0.8' '/nix/store/1x1msj33z37b65vlxbs51l7i4j92qn9h-brotli-1.2.0-dev' '/nix/store/7ff90dag7i173s49c5m614wny2lpps1l-brotli-1.2.0-lib' '/nix/store/mj1k1nsdqr0mp9wsnkg7blgh3xf5wssv-brotli-1.2.0' '/nix/store/h176f4dhbcpj4lpf8sn28vdqp1mks5jk-libpng-apng-1.6.56-dev' '/nix/store/gsn3vddway3289p6mzy5shd1paly8dp4-libpng-apng-1.6.56' '/nix/store/zr22ggqbv79yv4y4wv06r4grla9h59yx-freetype-2.14.2' '/nix/store/gjg4aagfcn6r96c73rz4rwbclbdqqc6v-fontconfig-2.17.1-dev' '/nix/store/v18drszzvspk1wlq06r68nxgpn2b4cvd-fontconfig-2.17.1-bin' '/nix/store/bg6ms0vw071g1fdbx2my6bbzsk62p6vd-fontconfig-2.17.1-lib' '/nix/store/b63lk3n7piwf7a790c4cy0zinqi184fs-libjpeg-turbo-3.1.4-dev' '/nix/store/v70k3ch8rcw9b0la3axqb34dkyxqnx2s-libjpeg-turbo-3.1.4-bin' '/nix/store/lsln4vpc8spwmb96vjjmg4yd0krd2r7c-libjpeg-turbo-3.1.4' '/nix/store/5q46i43k18sspv8wjpasmrgl5n8y7j1s-openjpeg-2.5.4-dev' '/nix/store/nrq3pjzsjd4w9vcpgk4a2wfjlqz4xxzw-openjpeg-2.5.4' '/nix/store/8zhjvm4vixgvg089nn4wv7hhxlp7qg2c-cairo-1.18.4-dev' '/nix/store/hywlq1sf1prbyrhqwf2sbamazp1hghk1-pixman-0.46.4' '/nix/store/1kx6y7spy0q6372hqrvib7mw21gaq5bq-libxext-1.3.7-dev' '/nix/store/mvyxqkpyj2mgymljzj9bqi9bmz7ca5fk-xorgproto-2025.1' '/nix/store/hd6i8dzybk2jqwqh6frarw30w15yqq9b-libxau-1.0.12-dev' '/nix/store/2krkc90x3ch0mgkk48fxlglq14nqapdr-libxau-1.0.12' '/nix/store/n1ykqk7ibmp4h5r4x5fng4cn9wjlgj9y-libxext-1.3.7' '/nix/store/94m0129pm3jlbg4fj8py92j1vi870m9c-libxrender-0.9.12-dev' '/nix/store/4303g76pqhl7r8a2xvci0b4bj47bfbjz-libx11-1.8.13-dev' '/nix/store/5m91jqg1526jzsahrgmd37k4ml3nc5l4-libx11-1.8.13' '/nix/store/dwavjjnzjmp7901n2s61kw40qw8c5rfc-libxrender-0.9.12' '/nix/store/x44m80ahg51pz32dr0j39yzsr7bn7d5v-libxcb-1.17.0-dev' '/nix/store/fc1g44pg3i10wfzh3gb4m54pfgclsn76-libxcb-1.17.0' '/nix/store/kw0yjwbvw6arwgwaa3p8rz46qsgy4626-glib-2.86.3-dev' '/nix/store/lg8kfrcxy4bcwnlwbfn6x3s48k4aawba-libffi-3.5.2-dev' '/nix/store/hyai3q7gvdfppw4ky7s2mvhxvfyp5bh7-libffi-3.5.2' '/nix/store/ypj27q94ay0ybq9aa14gk0cxjv9d7z4m-gettext-1.0' '/nix/store/5722rfnbamx35h5df4wlvlqrmvmaan7i-glibc-iconv-2.42' '/nix/store/b9jcqjd8gnxr87p7wc91lmbyd90kzlc1-glib-2.86.3-bin' '/nix/store/zcmsivndca5wmam9nwnbjrm0zkgykwfz-glib-2.86.3' '/nix/store/hgvr4xvcqm4a06rq5scgcy6nlk5q89gd-cairo-1.18.4' '/nix/store/pbyr7jlx85a0vlx623jqjd18cnccb5vv-lcms2-2.18-dev' '/nix/store/xiq38z94b68c8dgj7nfx9xlh2984c2mp-lcms2-2.18-bin' '/nix/store/3j2yd136zgln9w2hsrvlmazyrhcnfri5-lcms2-2.18' '/nix/store/ankisnmp03gzp9m0z4bqy1i2ar23wb48-libtiff-4.7.1-dev' '/nix/store/cbdy1d44cqa9j7x0ga72dqsk4p49ih70-libtiff-4.7.1-bin' '/nix/store/6w9m0a1v9kx40q341wq4y337s8csqhyn-libtiff-4.7.1' '/nix/store/7xvb5060qcf36ncp47wz62rl3fsccv1g-curl-8.19.0-dev' '/nix/store/dgdzsx6i729gcp1rrz85zbaacgl86gab-krb5-1.22.1-dev' '/nix/store/8cr60j6q7rqmcy4k8l6l1cay9579kd6y-krb5-1.22.1-lib' '/nix/store/qp2qzmh67rqy6i36sh3iqznk1akiw4q1-krb5-1.22.1' '/nix/store/iaf80mkaj9kfgy3h6hf1xqj7la8acr7y-nghttp2-1.68.1-dev' '/nix/store/hms747x82q23p2g6r6kgzqf7li2ryk39-nghttp2-1.68.1-lib' '/nix/store/yvxyaqh3bzj7nr64zlr1axyf76fgcszb-nghttp2-1.68.1' '/nix/store/d2xhslm8a0b1lk0p4plmyip3i194znhy-nghttp3-1.15.0-dev' '/nix/store/133x0z91pizyk8zr4l2ccgqlclpkp1lj-nghttp3-1.15.0' '/nix/store/yp754aaxmfqdag95053yax1fdaa4s9ck-ngtcp2-1.22.0-dev' '/nix/store/g5sd94mk8w1a0wiipk81ri0prk136d32-ngtcp2-1.22.0' '/nix/store/j3ypygy4pwwgkdrkxkhnhxqkwx4yw8zq-libidn2-2.3.8-dev' '/nix/store/a327a5lqzwakcs3yjgx4sa1931fph5gf-libidn2-2.3.8-bin' '/nix/store/sgswwrxkhdlfskklqp4gsbi2cskfg07c-libidn2-2.3.8' '/nix/store/dy64cxaygvmjfznysgxk501yds8jij6s-openssl-3.6.1-dev' '/nix/store/2di90l89y2ygdy3rbws7dhg9nrvd3pnx-openssl-3.6.1-bin' '/nix/store/wbyqkb1vpm41s4jb8pv0i9h4jv08xdrv-openssl-3.6.1' '/nix/store/ylldnaarbvwkvpn5dasnjjyvvghh6k3r-libpsl-0.21.5-dev' '/nix/store/g6q58mbnmi0f05xpm9nfvfhq963yv7wv-publicsuffix-list-0-unstable-2026-03-26' '/nix/store/79kr7fafcvvmch13cyczpckz40159pk5-libpsl-0.21.5' '/nix/store/5c04s19in4y2ij0zzkh4y9gqys8rwgc4-libssh2-1.11.1-dev' '/nix/store/9lzm6krq5ikzbqbmazbh5jmzwph99rz3-libssh2-1.11.1' '/nix/store/vbqakw4shfcbmdxs6kkp3jmp9k5br94y-zstd-1.5.7-dev' '/nix/store/91jddg4g6788ilnk3kww8j8jhxhzk6d3-zstd-1.5.7-bin' '/nix/store/k0rqiflg1vkn1kj96br5pfxj40p3srz4-zstd-1.5.7' '/nix/store/sm2nq18jjqp4x0sxpl6lrvwl9rx6mvj2-curl-8.19.0-bin' '/nix/store/pz6b64891m180yb4hadj1jjg3wm3ybng-curl-8.19.0' '/nix/store/xafb1qxw69j6fg1s8ln2drppm2zjjfr5-nss-3.112.3-dev' '/nix/store/3qfr4jp73jac5rnkx8xj58whv4yc80zy-nspr-4.38.2-dev' '/nix/store/amjf7cch3hb5r6l646mwjhrr9384ks4s-nspr-4.38.2' '/nix/store/0wnl2h5xgy1q7bgkqdbiyzxnrq3cmigi-nss-3.112.3' '/nix/store/92ipcswac970qz2iq0nn1yw1jj69xm69-poppler-utils-25.10.0' '/nix/store/l7nryi3685lc6di1wbyfmb5q3v3xmfqz-ghostscript-with-X-10.06.0' '/nix/store/hn59rqwq5j0z7l13yns903l6ibylwz1g-imagemagick-7.1.2-19-dev' '/nix/store/vd0i6w0g7wgj621lpzc2dsld42fsvh6c-libxt-1.3.1-dev' '/nix/store/sl65d0g3k4f6v5w7xclx334zzcj1w533-libsm-1.2.6-dev' '/nix/store/07rdpwd0gxa48k7p7p9mk6h0s0p5zknc-libice-1.1.2-dev' '/nix/store/qhw8zihdm481cvia6pd0kl2fmqk9mr2k-libice-1.1.2' '/nix/store/wnmwabsnj34j46c579y0ypc29xjfxjwf-libsm-1.2.6' '/nix/store/vqisl3q8b600dhrpj2a12bk4r5vzn3g4-libxt-1.3.1' '/nix/store/vdz5z5d4qvsfqdafihrfwzi5r7wr24lk-libwebp-1.6.0' '/nix/store/wgz6lg6jd6rq3n7gxgaj8i9qm6f5xlbf-fftw-double-3.3.10-dev' '/nix/store/84crpkdlv33nx4kahqzkss83fvpp8x3q-fftw-double-3.3.10' '/nix/store/pjcg9z9zj4hqa7y8jjgsx06rc31q6r8s-imagemagick-7.1.2-19' '/nix/store/p8x5zv9s9qg3ld8b7jdm03hkpdqybjl9-jq-1.8.1-dev' '/nix/store/v5c3inhfq6xshmwg1c254vfbcy4jp3k9-jq-1.8.1-bin' '/nix/store/09bq2i0kb008ccg3qdbyxv81ggxxnn09-jq-1.8.1' '/nix/store/9xkb4la9kpnsbrs3kw2cij3wjfbv6j6g-duckdb-1.5.2-dev' '/nix/store/kqjjmmq70c07hpizbd2sprryrx6a7bs5-duckdb-1.5.2-lib' '/nix/store/n4h91v3p9v5hfgcrmfashil26nsrsrhs-duckdb-1.5.2' '/nix/store/jx6bzribg9fa0mxbr8b602rq74k24dr7-python3.13-yamllint-1.37.1' '/nix/store/jl0mxihyizv77l66mzbvmv49iiri72sd-python3.13-pyyaml-6.0.3' '/nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12' '/nix/store/pdjdz9mqsj6az0znlrgh2fj6wp1rb032-python3.13-pathspec-0.12.1' '/nix/store/09hk83dw55dpbw1f8km58pycmbfr186k-shellcheck-0.11.0' '/nix/store/7xiiq153kv13wcqb6j5zffz2g778nssv-shellcheck-0.11.0-bin' '/nix/store/hn7cpgmj18mx8lj5wsnjgcy158cnfyz1-statix-0.5.8' '/nix/store/ivy6wb23x19x29qz49y98amkch1jbz84-elan-4.2.1' '/nix/store/xiy3ydpzw5bdqqd7ri8qbg3bn4r2qxg1-rustup-1.29.0' '/nix/store/biagcw4fwc90ala8pxbdb919khj39rzy-clang-wrapper-19.1.7' '/nix/store/vr4sjc5ajni6j76wqkvkx84q141270ak-binutils-wrapper-2.46' '/nix/store/xswd8j43wkqpadsgfl3cnf1hibvwncrw-lld-19.1.7-dev' '/nix/store/477l7v6l11yw7vc1gzmv8ybjl8rs799z-lld-19.1.7-lib' '/nix/store/hvihdgv65b31lrw3rdybjz1m8q314qyi-lld-19.1.7' '/nix/store/v2i1hgv567g3v91im5x4g5bff52143i0-cmake-4.1.2' '/nix/store/v7mjkia7ki79s5i24ldbzq1khalhgzk0-pkg-config-wrapper-0.29.2' '/nix/store/fszv4kq85ywrpq6dy2wydl1ggkbc6sjp-emscripten-5.0.6' '/nix/store/pxhpmfr4qwihzxqam9642a9r7jpvbblr-typescript-5.9.3' '/nix/store/246dw7jxjgznw9fql388hj43yyknlqmn-vscode-1.116.0' '/nix/store/9lhr1c3l9qzv8pzp3idmii1nwvxxjys3-gzip-1.14' '/nix/store/x78aqw188hv2nmj8hbbl4q9knhns4qf2-xz-5.8.3-dev' '/nix/store/2nm5c858fh52s6mhcffm07s3biaxys44-xz-5.8.3-bin' '/nix/store/hmslvsxvs2ijb7iw5krdckai2im6vp2y-xz-5.8.3' '/nix/store/i7arixgp0p933iicqzfza1dm9g2vgbzf-lz4-1.10.0-dev' '/nix/store/fy28r1ynjk65gnj898k9dabyvzz9mryc-lz4-1.10.0-lib' '/nix/store/m7m89ms25namgzbhcx6nf42jgjx55lcx-lz4-1.10.0' '/nix/store/qpf8bnaad0j8g4ggl65hvfs8l5y1alwp-mermaid-cli-11.12.0' '/nix/store/nkai8ssk915yc9mvj0xi28zliwwsaacp-zpaq-7.15' '/nix/store/0l71d5r282xjml5zhd3knf4syinczqwh-R-4.5.3-wrapper' )
declare -a pkgsTargetTarget=('/nix/store/sw1dgmpi3s1vkjfbdjwj4bliz626fvqp-compiler-rt-libc-19.1.7-dev' '/nix/store/9agl8i5ax5w0x01rsgazhizhgpshb8pg-compiler-rt-libc-19.1.7' )
declare -a postFixupHooks=('noBrokenSymlinksInAllOutputs' '_makeSymlinksRelative' '_multioutPropagateDev' 'cmakePcfileCheckPhase' )
declare -a postHooks=('makeCmakeFindLibs' )
declare -a postInstallHooks=('glibPostInstallHook' )
declare -a postUnpackHooks=('_updateSourceDateEpochFromSourceRoot' )
declare -a preConfigureHooks=('_multioutConfig' )
preConfigurePhases=' updateAutotoolsGnuConfigScriptsPhase'
declare -a preFixupHooks=('_moveToShare' '_multioutDocs' '_multioutDevs' )
preInstallPhases=' glibPreInstallPhase'
preferLocalBuild='1'
export preferLocalBuild
prefix='/extra/iohk/claude-env/outputs/out'
declare -a propagatedBuildDepFiles=('propagated-build-build-deps' 'propagated-native-build-inputs' 'propagated-build-target-deps' )
propagatedBuildInputs=''
export propagatedBuildInputs
declare -a propagatedHostDepFiles=('propagated-host-host-deps' 'propagated-build-inputs' )
propagatedNativeBuildInputs=''
export propagatedNativeBuildInputs
declare -a propagatedTargetDepFiles=('propagated-target-target-deps' )
role_post=''
setOutputFlags=''
shell='/nix/store/i27rhb3nr65rkrwz36bchkwmav6ggsmn-bash-5.3p9/bin/bash'
export shell
shellHook='export PS1=$(printf '\''\n\001\033[1;32m\002[nix develop:\\w]\\$\001\033[0m\002 '\'')
# elan stores per-toolchain state under $ELAN_HOME (default
# ~/.elan). Override here if a project-local cache is preferred.
export ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
# rustup stores per-toolchain state under $RUSTUP_HOME (default
# ~/.rustup), and installs cargo/rustc shims under
# $CARGO_HOME/bin (default ~/.cargo/bin). Same per-user cache
# pattern as elan/Emscripten. `rustup default stable` on first
# entry to populate; individual projects can pin via
# rust-toolchain.toml.
export RUSTUP_HOME="${RUSTUP_HOME:-$HOME/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$HOME/.cargo}"
export PATH="$CARGO_HOME/bin:$PATH"
# Emscripten needs a writable cache; the nixpkgs wrapper points
# at a read-only store path by default. Redirect to a per-user
# cache directory.
export EM_CACHE="${EM_CACHE:-$HOME/.cache/emscripten}"
# Substrate build tooling. bindgen-using crates (rocksdb-sys,
# secp256k1-sys) need $LIBCLANG_PATH so they can locate libclang.
# secp256k1-sys'\''s build.rs compiles C for wasm32v1-none; point
# CC_wasm32v1_none / AR_wasm32v1_none at LLVM tooling so the
# -mcpu=mvp / -mmutable-globals flags parse correctly.
#
# NB: use the UNWRAPPED clang for the wasm-target CC. Nix'\''s
# cc-wrapper injects hardening flags (`-fzero-call-used-regs=used-gpr`)
# that clang rejects when compiling for wasm32-unknown-unknown.
# It also silently pulls in host glibc headers, which then fail
# on `gnu/stubs-32.h` because we don'\''t have 32-bit stubs. The
# unwrapped clang avoids both.
#
# BUT — nix splits the unwrapped clang derivation into `bin`
# (the compiler binary) and `.lib` (the resource-dir headers
# like stddef.h). Clang'\''s baked-in -resource-dir points inside
# its bin output where headers don'\''t exist. Override via
# CFLAGS_wasm32v1_none to redirect at the .lib output.
#
# The `19` version segment tracks llvmPackages_19; bump both
# together on LLVM upgrades.
#
# See experiments/instrumented-node/lessons-learned.md.
export LIBCLANG_PATH="/nix/store/r2sjvsxdf8713jqm3v4rrqg73ji087q0-clang-19.1.7-lib/lib"
export CC_wasm32v1_none="/nix/store/8xnhbkhlxvg9b4703lds4mirmipws2gf-clang-19.1.7/bin/clang"
export AR_wasm32v1_none="/nix/store/7rmlrv4izc3pycxcjx9dxs20iqqhnmcs-llvm-19.1.7/bin/llvm-ar"
export CFLAGS_wasm32v1_none="-resource-dir=/nix/store/r2sjvsxdf8713jqm3v4rrqg73ji087q0-clang-19.1.7-lib/lib/clang/19"
'
export shellHook
stdenv='/nix/store/w708nqm6lvvikrq8d3x45g96hzfij0r8-stdenv-linux'
export stdenv
strictDeps=''
export strictDeps
system='x86_64-linux'
export system
declare -a unpackCmdHooks=('_defaultUnpack' )
_activatePkgs ()
{
 
    local hostOffset targetOffset;
    local pkg;
    for hostOffset in "${allPlatOffsets[@]}";
    do
        local pkgsVar="${pkgAccumVarVars[hostOffset + 1]}";
        for targetOffset in "${allPlatOffsets[@]}";
        do
            (( hostOffset <= targetOffset )) || continue;
            local pkgsRef="${pkgsVar}[$targetOffset - $hostOffset]";
            local pkgsSlice="${!pkgsRef}[@]";
            for pkg in ${!pkgsSlice+"${!pkgsSlice}"};
            do
                activatePackage "$pkg" "$hostOffset" "$targetOffset";
            done;
        done;
    done
}
_addRpathPrefix ()
{
 
    if [ "${NIX_NO_SELF_RPATH:-0}" != 1 ]; then
        export NIX_LDFLAGS="-rpath $1/lib ${NIX_LDFLAGS-}";
    fi
}
_addToEnv ()
{
 
    local depHostOffset depTargetOffset;
    local pkg;
    for depHostOffset in "${allPlatOffsets[@]}";
    do
        local hookVar="${pkgHookVarVars[depHostOffset + 1]}";
        local pkgsVar="${pkgAccumVarVars[depHostOffset + 1]}";
        for depTargetOffset in "${allPlatOffsets[@]}";
        do
            (( depHostOffset <= depTargetOffset )) || continue;
            local hookRef="${hookVar}[$depTargetOffset - $depHostOffset]";
            if [[ -z "${strictDeps-}" ]]; then
                local visitedPkgs="";
                for pkg in "${pkgsBuildBuild[@]}" "${pkgsBuildHost[@]}" "${pkgsBuildTarget[@]}" "${pkgsHostHost[@]}" "${pkgsHostTarget[@]}" "${pkgsTargetTarget[@]}";
                do
                    if [[ "$visitedPkgs" = *"$pkg"* ]]; then
                        continue;
                    fi;
                    runHook "${!hookRef}" "$pkg";
                    visitedPkgs+=" $pkg";
                done;
            else
                local pkgsRef="${pkgsVar}[$depTargetOffset - $depHostOffset]";
                local pkgsSlice="${!pkgsRef}[@]";
                for pkg in ${!pkgsSlice+"${!pkgsSlice}"};
                do
                    runHook "${!hookRef}" "$pkg";
                done;
            fi;
        done;
    done
}
_allFlags ()
{
 
    export system pname name version;
    while IFS='' read -r varName; do
        nixTalkativeLog "@${varName}@ -> ${!varName}";
        args+=("--subst-var" "$varName");
    done < <(awk 'BEGIN { for (v in ENVIRON) if (v ~ /^[a-z][a-zA-Z0-9_]*$/) print v }')
}
_assignFirst ()
{
 
    local varName="$1";
    local _var;
    local REMOVE=REMOVE;
    shift;
    for _var in "$@";
    do
        if [ -n "${!_var-}" ]; then
            eval "${varName}"="${_var}";
            return;
        fi;
    done;
    echo;
    echo "error: _assignFirst: could not find a non-empty variable whose name to assign to ${varName}.";
    echo "       The following variables were all unset or empty:";
    echo "           $*";
    if [ -z "${out:-}" ]; then
        echo '       If you do not want an "out" output in your derivation, make sure to define';
        echo '       the other specific required outputs. This can be achieved by picking one';
        echo "       of the above as an output.";
        echo '       You do not have to remove "out" if you want to have a different default';
        echo '       output, because the first output is taken as a default.';
        echo;
    fi;
    return 1
}
_callImplicitHook ()
{
 
    local def="$1";
    local hookName="$2";
    if declare -F "$hookName" > /dev/null; then
        nixTalkativeLog "calling implicit '$hookName' function hook";
        "$hookName";
    else
        if type -p "$hookName" > /dev/null; then
            nixTalkativeLog "sourcing implicit '$hookName' script hook";
            source "$hookName";
        else
            if [ -n "${!hookName:-}" ]; then
                nixTalkativeLog "evaling implicit '$hookName' string hook";
                eval "${!hookName}";
            else
                return "$def";
            fi;
        fi;
    fi
}
_defaultUnpack ()
{
 
    local fn="$1";
    local destination;
    if [ -d "$fn" ]; then
        destination="$(stripHash "$fn")";
        if [ -e "$destination" ]; then
            echo "Cannot copy $fn to $destination: destination already exists!";
            echo "Did you specify two \"srcs\" with the same \"name\"?";
            return 1;
        fi;
        cp -r --preserve=timestamps --reflink=auto -- "$fn" "$destination";
    else
        case "$fn" in 
            *.tar.xz | *.tar.lzma | *.txz)
                ( XZ_OPT="--threads=$NIX_BUILD_CORES" xz -d < "$fn";
                true ) | tar xf - --mode=+w --warning=no-timestamp
            ;;
            *.tar | *.tar.* | *.tgz | *.tbz2 | *.tbz)
                tar xf "$fn" --mode=+w --warning=no-timestamp
            ;;
            *)
                return 1
            ;;
        esac;
    fi
}
_doStrip ()
{
 
    local -ra flags=(dontStripHost dontStripTarget);
    local -ra debugDirs=(stripDebugList stripDebugListTarget);
    local -ra allDirs=(stripAllList stripAllListTarget);
    local -ra stripCmds=(STRIP STRIP_FOR_TARGET);
    local -ra ranlibCmds=(RANLIB RANLIB_FOR_TARGET);
    stripDebugList=${stripDebugList[*]:-lib lib32 lib64 libexec bin sbin Applications Library/Frameworks};
    stripDebugListTarget=${stripDebugListTarget[*]:-};
    stripAllList=${stripAllList[*]:-};
    stripAllListTarget=${stripAllListTarget[*]:-};
    local i;
    for i in ${!stripCmds[@]};
    do
        local -n flag="${flags[$i]}";
        local -n debugDirList="${debugDirs[$i]}";
        local -n allDirList="${allDirs[$i]}";
        local -n stripCmd="${stripCmds[$i]}";
        local -n ranlibCmd="${ranlibCmds[$i]}";
        if [[ -n "${dontStrip-}" || -n "${flag-}" ]] || ! type -f "${stripCmd-}" 2> /dev/null 1>&2; then
            continue;
        fi;
        stripDirs "$stripCmd" "$ranlibCmd" "$debugDirList" "${stripDebugFlags[*]:--S -p}";
        stripDirs "$stripCmd" "$ranlibCmd" "$allDirList" "${stripAllFlags[*]:--s -p}";
    done
}
_eval ()
{
 
    if declare -F "$1" > /dev/null 2>&1; then
        "$@";
    else
        eval "$1";
    fi
}
_logHook ()
{
 
    if [[ -z ${NIX_LOG_FD-} ]]; then
        return;
    fi;
    local hookKind="$1";
    local hookExpr="$2";
    shift 2;
    if declare -F "$hookExpr" > /dev/null 2>&1; then
        nixTalkativeLog "calling '$hookKind' function hook '$hookExpr'" "$@";
    else
        if type -p "$hookExpr" > /dev/null; then
            nixTalkativeLog "sourcing '$hookKind' script hook '$hookExpr'";
        else
            if [[ "$hookExpr" != "_callImplicitHook"* ]]; then
                local exprToOutput;
                if [[ ${NIX_DEBUG:-0} -ge 5 ]]; then
                    exprToOutput="$hookExpr";
                else
                    local hookExprLine;
                    while IFS= read -r hookExprLine; do
                        hookExprLine="${hookExprLine#"${hookExprLine%%[![:space:]]*}"}";
                        if [[ -n "$hookExprLine" ]]; then
                            exprToOutput+="$hookExprLine\\n ";
                        fi;
                    done <<< "$hookExpr";
                    exprToOutput="${exprToOutput%%\\n }";
                fi;
                nixTalkativeLog "evaling '$hookKind' string hook '$exprToOutput'";
            fi;
        fi;
    fi
}
_makeSymlinksRelative ()
{
 
    local prefixes;
    prefixes=();
    for output in $(getAllOutputNames);
    do
        [ ! -e "${!output}" ] && continue;
        prefixes+=("${!output}");
    done;
    find "${prefixes[@]}" -type l -printf '%H\0%p\0' | xargs -0 -n2 -r -P "$NIX_BUILD_CORES" sh -c '
      output="$1"
      link="$2"

      linkTarget=$(readlink "$link")

      # only touch links that point inside the same output tree
      [[ $linkTarget == "$output"/* ]] || exit 0

      if [ ! -e "$linkTarget" ]; then
        echo "the symlink $link is broken, it points to $linkTarget (which is missing)"
      fi

      echo "making symlink relative: $link"
      ln -snrf "$linkTarget" "$link"
    ' _
}
_moveLib64 ()
{
 
    if [ "${dontMoveLib64-}" = 1 ]; then
        return;
    fi;
    if [ ! -e "$prefix/lib64" -o -L "$prefix/lib64" ]; then
        return;
    fi;
    echo "moving $prefix/lib64/* to $prefix/lib";
    mkdir -p $prefix/lib;
    shopt -s dotglob;
    for i in $prefix/lib64/*;
    do
        mv --no-clobber "$i" $prefix/lib;
    done;
    shopt -u dotglob;
    rmdir $prefix/lib64;
    ln -s lib $prefix/lib64
}
_moveSbin ()
{
 
    if [ "${dontMoveSbin-}" = 1 ]; then
        return;
    fi;
    if [ ! -e "$prefix/sbin" -o -L "$prefix/sbin" ]; then
        return;
    fi;
    echo "moving $prefix/sbin/* to $prefix/bin";
    mkdir -p $prefix/bin;
    shopt -s dotglob;
    for i in $prefix/sbin/*;
    do
        mv "$i" $prefix/bin;
    done;
    shopt -u dotglob;
    rmdir $prefix/sbin;
    ln -s bin $prefix/sbin
}
_moveSystemdUserUnits ()
{
 
    if [ "${dontMoveSystemdUserUnits:-0}" = 1 ]; then
        return;
    fi;
    if [ ! -e "${prefix:?}/lib/systemd/user" ]; then
        return;
    fi;
    local source="$prefix/lib/systemd/user";
    local target="$prefix/share/systemd/user";
    echo "moving $source/* to $target";
    mkdir -p "$target";
    ( shopt -s dotglob;
    for i in "$source"/*;
    do
        mv "$i" "$target";
    done );
    rmdir "$source";
    ln -s "$target" "$source"
}
_moveToShare ()
{
 
    if [ -n "$__structuredAttrs" ]; then
        if [ -z "${forceShare-}" ]; then
            forceShare=(man doc info);
        fi;
    else
        forceShare=(${forceShare:-man doc info});
    fi;
    if [[ -z "$out" ]]; then
        return;
    fi;
    for d in "${forceShare[@]}";
    do
        if [ -d "$out/$d" ]; then
            if [ -d "$out/share/$d" ]; then
                echo "both $d/ and share/$d/ exist!";
            else
                echo "moving $out/$d to $out/share/$d";
                mkdir -p $out/share;
                mv $out/$d $out/share/;
            fi;
        fi;
    done
}
_multioutConfig ()
{
 
    if [ "$(getAllOutputNames)" = "out" ] || [ -z "${setOutputFlags-1}" ]; then
        return;
    fi;
    if [ -z "${shareDocName:-}" ]; then
        local confScript="${configureScript:-}";
        if [ -z "$confScript" ] && [ -x ./configure ]; then
            confScript=./configure;
        fi;
        if [ -f "$confScript" ]; then
            local shareDocName="$(sed -n "s/^PACKAGE_TARNAME='\(.*\)'$/\1/p" < "$confScript")";
        fi;
        if [ -z "$shareDocName" ] || echo "$shareDocName" | grep -q '[^a-zA-Z0-9_-]'; then
            shareDocName="$(echo "$name" | sed 's/-[^a-zA-Z].*//')";
        fi;
    fi;
    prependToVar configureFlags --bindir="${!outputBin}"/bin --sbindir="${!outputBin}"/sbin --includedir="${!outputInclude}"/include --mandir="${!outputMan}"/share/man --infodir="${!outputInfo}"/share/info --docdir="${!outputDoc}"/share/doc/"${shareDocName}" --libdir="${!outputLib}"/lib --libexecdir="${!outputLib}"/libexec --localedir="${!outputLib}"/share/locale;
    prependToVar installFlags pkgconfigdir="${!outputDev}"/lib/pkgconfig m4datadir="${!outputDev}"/share/aclocal aclocaldir="${!outputDev}"/share/aclocal
}
_multioutDevs ()
{
 
    if [ "$(getAllOutputNames)" = "out" ] || [ -z "${moveToDev-1}" ]; then
        return;
    fi;
    moveToOutput include "${!outputInclude}";
    moveToOutput lib/pkgconfig "${!outputDev}";
    moveToOutput share/pkgconfig "${!outputDev}";
    moveToOutput lib/cmake "${!outputDev}";
    moveToOutput share/aclocal "${!outputDev}";
    for f in "${!outputDev}"/{lib,share}/pkgconfig/*.pc;
    do
        echo "Patching '$f' includedir to output ${!outputInclude}";
        sed -i "/^includedir=/s,=\${prefix},=${!outputInclude}," "$f";
    done
}
_multioutDocs ()
{
 
    local REMOVE=REMOVE;
    moveToOutput share/info "${!outputInfo}";
    moveToOutput share/doc "${!outputDoc}";
    moveToOutput share/gtk-doc "${!outputDevdoc}";
    moveToOutput share/devhelp/books "${!outputDevdoc}";
    moveToOutput share/man "${!outputMan}";
    moveToOutput share/man/man3 "${!outputDevman}"
}
_multioutPropagateDev ()
{
 
    if [ "$(getAllOutputNames)" = "out" ]; then
        return;
    fi;
    local outputFirst;
    for outputFirst in $(getAllOutputNames);
    do
        break;
    done;
    local propagaterOutput="$outputDev";
    if [ -z "$propagaterOutput" ]; then
        propagaterOutput="$outputFirst";
    fi;
    if [ -z "${propagatedBuildOutputs+1}" ]; then
        local po_dirty="$outputBin $outputInclude $outputLib";
        set +o pipefail;
        propagatedBuildOutputs=`echo "$po_dirty"             | tr -s ' ' '\n' | grep -v -F "$propagaterOutput"             | sort -u | tr '\n' ' ' `;
        set -o pipefail;
    fi;
    if [ -z "$propagatedBuildOutputs" ]; then
        return;
    fi;
    mkdir -p "${!propagaterOutput}"/nix-support;
    for output in $propagatedBuildOutputs;
    do
        echo -n " ${!output}" >> "${!propagaterOutput}"/nix-support/propagated-build-inputs;
    done
}
_nixLogWithLevel ()
{
 
    [[ -z ${NIX_LOG_FD-} || ${NIX_DEBUG:-0} -lt ${1:?} ]] && return 0;
    local logLevel;
    case "${1:?}" in 
        0)
            logLevel=ERROR
        ;;
        1)
            logLevel=WARN
        ;;
        2)
            logLevel=NOTICE
        ;;
        3)
            logLevel=INFO
        ;;
        4)
            logLevel=TALKATIVE
        ;;
        5)
            logLevel=CHATTY
        ;;
        6)
            logLevel=DEBUG
        ;;
        7)
            logLevel=VOMIT
        ;;
        *)
            echo "_nixLogWithLevel: called with invalid log level: ${1:?}" >&"$NIX_LOG_FD";
            return 1
        ;;
    esac;
    local callerName="${FUNCNAME[2]}";
    if [[ $callerName == "_callImplicitHook" ]]; then
        callerName="${hookName:?}";
    fi;
    printf "%s: %s: %s\n" "$logLevel" "$callerName" "${2:?}" >&"$NIX_LOG_FD"
}
_overrideFirst ()
{
 
    if [ -z "${!1-}" ]; then
        _assignFirst "$@";
    fi
}
_pruneLibtoolFiles ()
{
 
    if [ "${dontPruneLibtoolFiles-}" ] || [ ! -e "$prefix" ]; then
        return;
    fi;
    find "$prefix" -type f -name '*.la' -exec grep -q '^# Generated by .*libtool' {} \; -exec grep -q "^old_library=''" {} \; -exec sed -i {} -e "/^dependency_libs='[^']/ c dependency_libs='' #pruned" \;
}
_updateSourceDateEpochFromSourceRoot ()
{
 
    if [ -n "$sourceRoot" ]; then
        updateSourceDateEpoch "$sourceRoot";
    fi
}
activatePackage ()
{
 
    local pkg="$1";
    local -r hostOffset="$2";
    local -r targetOffset="$3";
    (( hostOffset <= targetOffset )) || exit 1;
    if [ -f "$pkg" ]; then
        nixTalkativeLog "sourcing setup hook '$pkg'";
        source "$pkg";
    fi;
    if [[ -z "${strictDeps-}" || "$hostOffset" -le -1 ]]; then
        addToSearchPath _PATH "$pkg/bin";
    fi;
    if (( hostOffset <= -1 )); then
        addToSearchPath _XDG_DATA_DIRS "$pkg/share";
    fi;
    if [[ "$hostOffset" -eq 0 && -d "$pkg/bin" ]]; then
        addToSearchPath _HOST_PATH "$pkg/bin";
    fi;
    if [[ -f "$pkg/nix-support/setup-hook" ]]; then
        nixTalkativeLog "sourcing setup hook '$pkg/nix-support/setup-hook'";
        source "$pkg/nix-support/setup-hook";
    fi
}
addCMakeParams ()
{
 
    addToSearchPath NIXPKGS_CMAKE_PREFIX_PATH $1
}
addEnvHooks ()
{
 
    local depHostOffset="$1";
    shift;
    local pkgHookVarsSlice="${pkgHookVarVars[$depHostOffset + 1]}[@]";
    local pkgHookVar;
    for pkgHookVar in "${!pkgHookVarsSlice}";
    do
        eval "${pkgHookVar}s"'+=("$@")';
    done
}
addPythonPath ()
{
 
    addToSearchPathWithCustomDelimiter : PYTHONPATH $1/lib/python3.13/site-packages
}
addRLibPath ()
{
 
    if [[ -d "$1/library" ]]; then
        addToSearchPath R_LIBS_SITE "$1/library";
    fi
}
addToSearchPath ()
{
 
    addToSearchPathWithCustomDelimiter ":" "$@"
}
addToSearchPathWithCustomDelimiter ()
{
 
    local delimiter="$1";
    local varName="$2";
    local dir="$3";
    if [[ -d "$dir" && "${!varName:+${delimiter}${!varName}${delimiter}}" != *"${delimiter}${dir}${delimiter}"* ]]; then
        export "${varName}=${!varName:+${!varName}${delimiter}}${dir}";
    fi
}
appendToVar ()
{
 
    local -n nameref="$1";
    local useArray type;
    if [ -n "$__structuredAttrs" ]; then
        useArray=true;
    else
        useArray=false;
    fi;
    if type=$(declare -p "$1" 2> /dev/null); then
        case "${type#* }" in 
            -A*)
                echo "appendToVar(): ERROR: trying to use appendToVar on an associative array, use variable+=([\"X\"]=\"Y\") instead." 1>&2;
                return 1
            ;;
            -a*)
                useArray=true
            ;;
            *)
                useArray=false
            ;;
        esac;
    fi;
    shift;
    if $useArray; then
        nameref=(${nameref+"${nameref[@]}"} "$@");
    else
        nameref="${nameref-} $*";
    fi
}
auditTmpdir ()
{
 
    local dir="$1";
    [ -e "$dir" ] || return 0;
    echo "checking for references to $TMPDIR/ in $dir...";
    local tmpdir elf_fifo script_fifo;
    tmpdir="$(mktemp -d)";
    elf_fifo="$tmpdir/elf";
    script_fifo="$tmpdir/script";
    mkfifo "$elf_fifo" "$script_fifo";
    ( find "$dir" -type f -not -path '*/.build-id/*' -print0 | while IFS= read -r -d '' file; do
        if isELF "$file"; then
            printf '%s\0' "$file" 1>&3;
        else
            if isScript "$file"; then
                filename=${file##*/};
                dir=${file%/*};
                if [ -e "$dir/.$filename-wrapped" ]; then
                    printf '%s\0' "$file" 1>&4;
                fi;
            fi;
        fi;
    done;
    exec 3>&- 4>&- ) 3> "$elf_fifo" 4> "$script_fifo" & ( xargs -0 -r -P "$NIX_BUILD_CORES" -n 1 sh -c '
            if { printf :; patchelf --print-rpath "$1"; } | grep -q -F ":$TMPDIR/"; then
                echo "RPATH of binary $1 contains a forbidden reference to $TMPDIR/"
                exit 1
            fi
        ' _ < "$elf_fifo" ) & local pid_elf=$!;
    local pid_script;
    ( xargs -0 -r -P "$NIX_BUILD_CORES" -n 1 sh -c '
            if grep -q -F "$TMPDIR/" "$1"; then
                echo "wrapper script $1 contains a forbidden reference to $TMPDIR/"
                exit 1
            fi
        ' _ < "$script_fifo" ) & local pid_script=$!;
    wait "$pid_elf" || { 
        echo "Some binaries contain forbidden references to $TMPDIR/. Check the error above!";
        exit 1
    };
    wait "$pid_script" || { 
        echo "Some scripts contain forbidden references to $TMPDIR/. Check the error above!";
        exit 1
    };
    rm -r "$tmpdir"
}
bintoolsWrapper_addLDVars ()
{
 
    local role_post;
    getHostRoleEnvHook;
    if [[ -d "$1/lib64" && ! -L "$1/lib64" ]]; then
        export NIX_LDFLAGS${role_post}+=" -L$1/lib64";
    fi;
    if [[ -d "$1/lib" ]]; then
        local -a glob=($1/lib/lib*);
        if [ "${#glob[*]}" -gt 0 ]; then
            export NIX_LDFLAGS${role_post}+=" -L$1/lib";
        fi;
    fi
}
buildPhase ()
{
 
    runHook preBuild;
    if [[ -z "${makeFlags-}" && -z "${makefile:-}" && ! ( -e Makefile || -e makefile || -e GNUmakefile ) ]]; then
        echo "no Makefile or custom buildPhase, doing nothing";
    else
        foundMakefile=1;
        local flagsArray=(${enableParallelBuilding:+-j${NIX_BUILD_CORES}} SHELL="$SHELL");
        concatTo flagsArray makeFlags makeFlagsArray buildFlags buildFlagsArray;
        echoCmd 'build flags' "${flagsArray[@]}";
        make ${makefile:+-f $makefile} "${flagsArray[@]}";
        unset flagsArray;
    fi;
    runHook postBuild
}
ccWrapper_addCVars ()
{
 
    local role_post;
    getHostRoleEnvHook;
    local found=;
    if [ -d "$1/include" ]; then
        export NIX_CFLAGS_COMPILE${role_post}+=" -isystem $1/include";
        found=1;
    fi;
    if [ -d "$1/Library/Frameworks" ]; then
        export NIX_CFLAGS_COMPILE${role_post}+=" -iframework $1/Library/Frameworks";
        found=1;
    fi;
    if [[ -n "1" && -n ${NIX_STORE:-} && -n $found ]]; then
        local scrubbed="$NIX_STORE/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee-${1#"$NIX_STORE"/*-}";
        export NIX_CFLAGS_COMPILE${role_post}+=" -fmacro-prefix-map=$1=$scrubbed";
    fi
}
checkPhase ()
{
 
    runHook preCheck;
    if [[ -z "${foundMakefile:-}" ]]; then
        echo "no Makefile or custom checkPhase, doing nothing";
        runHook postCheck;
        return;
    fi;
    if [[ -z "${checkTarget:-}" ]]; then
        if make -n ${makefile:+-f $makefile} check > /dev/null 2>&1; then
            checkTarget="check";
        else
            if make -n ${makefile:+-f $makefile} test > /dev/null 2>&1; then
                checkTarget="test";
            fi;
        fi;
    fi;
    if [[ -z "${checkTarget:-}" ]]; then
        echo "no check/test target in ${makefile:-Makefile}, doing nothing";
    else
        local flagsArray=(${enableParallelChecking:+-j${NIX_BUILD_CORES}} SHELL="$SHELL");
        concatTo flagsArray makeFlags makeFlagsArray checkFlags=VERBOSE=y checkFlagsArray checkTarget;
        echoCmd 'check flags' "${flagsArray[@]}";
        make ${makefile:+-f $makefile} "${flagsArray[@]}";
        unset flagsArray;
    fi;
    runHook postCheck
}
cmakeConfigurePhase ()
{
 
    runHook preConfigure;
    : ${cmakeBuildDir:=build};
    export CTEST_OUTPUT_ON_FAILURE=1;
    if [ -n "${enableParallelChecking-1}" ]; then
        export CTEST_PARALLEL_LEVEL=$NIX_BUILD_CORES;
    fi;
    if [ -z "${dontUseCmakeBuildDir-}" ]; then
        mkdir -p "$cmakeBuildDir";
        cd "$cmakeBuildDir";
        : ${cmakeDir:=..};
    else
        : ${cmakeDir:=.};
    fi;
    if [ -z "${dontAddPrefix-}" ]; then
        prependToVar cmakeFlags "-DCMAKE_INSTALL_PREFIX=$prefix";
    fi;
    prependToVar cmakeFlags "-DCMAKE_CXX_COMPILER=$CXX";
    prependToVar cmakeFlags "-DCMAKE_C_COMPILER=$CC";
    prependToVar cmakeFlags "-DCMAKE_AR=$(command -v $AR)";
    prependToVar cmakeFlags "-DCMAKE_RANLIB=$(command -v $RANLIB)";
    prependToVar cmakeFlags "-DCMAKE_STRIP=$(command -v $STRIP)";
    prependToVar cmakeFlags "-DCMAKE_INSTALL_NAME_DIR=${!outputLib}/lib";
    if [[ -z "$shareDocName" ]]; then
        local cmakeLists="${cmakeDir}/CMakeLists.txt";
        if [[ -f "$cmakeLists" ]]; then
            local shareDocName="$(grep --only-matching --perl-regexp --ignore-case '\bproject\s*\(\s*"?\K([^[:space:]")]+)' < "$cmakeLists" | head -n1)";
        fi;
        if [[ -z "$shareDocName" ]] || echo "$shareDocName" | grep -q '[^a-zA-Z0-9_+-]'; then
            if [[ -n "${pname-}" ]]; then
                shareDocName="$pname";
            else
                shareDocName="$(echo "$name" | sed 's/-[^a-zA-Z].*//')";
            fi;
        fi;
    fi;
    prependToVar cmakeFlags "-DCMAKE_INSTALL_BINDIR=${!outputBin}/bin";
    prependToVar cmakeFlags "-DCMAKE_INSTALL_SBINDIR=${!outputBin}/sbin";
    prependToVar cmakeFlags "-DCMAKE_INSTALL_INCLUDEDIR=${!outputInclude}/include";
    prependToVar cmakeFlags "-DCMAKE_INSTALL_MANDIR=${!outputMan}/share/man";
    prependToVar cmakeFlags "-DCMAKE_INSTALL_INFODIR=${!outputInfo}/share/info";
    prependToVar cmakeFlags "-DCMAKE_INSTALL_DOCDIR=${!outputDoc}/share/doc/${shareDocName}";
    prependToVar cmakeFlags "-DCMAKE_INSTALL_LIBDIR=${!outputLib}/lib";
    prependToVar cmakeFlags "-DCMAKE_INSTALL_LIBEXECDIR=${!outputLib}/libexec";
    prependToVar cmakeFlags "-DCMAKE_INSTALL_LOCALEDIR=${!outputLib}/share/locale";
    if [ -z "${doCheck-}" ]; then
        prependToVar cmakeFlags "-DBUILD_TESTING=OFF";
    fi;
    prependToVar cmakeFlags "-DCMAKE_BUILD_TYPE=${cmakeBuildType:-Release}";
    prependToVar cmakeFlags "-DCMAKE_EXPORT_NO_PACKAGE_REGISTRY=ON";
    prependToVar cmakeFlags "-DCMAKE_FIND_USE_PACKAGE_REGISTRY=OFF";
    prependToVar cmakeFlags "-DCMAKE_FIND_USE_SYSTEM_PACKAGE_REGISTRY=OFF";
    if [ "${buildPhase-}" = ninjaBuildPhase ]; then
        prependToVar cmakeFlags "-GNinja";
    fi;
    local flagsArray=();
    concatTo flagsArray cmakeFlags cmakeFlagsArray;
    echoCmd 'cmake flags' "${flagsArray[@]}";
    cmake "$cmakeDir" "${flagsArray[@]}";
    if ! [[ -v enableParallelBuilding ]]; then
        enableParallelBuilding=1;
        echo "cmake: enabled parallel building";
    fi;
    if [[ "$enableParallelBuilding" -ne 0 ]]; then
        export CMAKE_BUILD_PARALLEL_LEVEL=$NIX_BUILD_CORES;
    fi;
    if ! [[ -v enableParallelInstalling ]]; then
        enableParallelInstalling=1;
        echo "cmake: enabled parallel installing";
    fi;
    runHook postConfigure
}
cmakePcfileCheckPhase ()
{
 
    while IFS= read -rd '' file; do
        grepout=$(grep --line-number '}//nix/store' "$file" || true);
        if [ -n "$grepout" ]; then
            { 
                echo "Broken paths found in a .pc file! $file";
                echo "The following lines have issues (specifically '//' in paths).";
                echo "$grepout";
                echo "It is very likely that paths are being joined improperly.";
                echo 'ex: "${prefix}/@CMAKE_INSTALL_LIBDIR@" should be "@CMAKE_INSTALL_FULL_LIBDIR@"';
                echo "Please see https://github.com/NixOS/nixpkgs/issues/144170 for more details.";
                exit 1
            } 1>&2;
        fi;
    done < <(find "${!outputDev}" -iname "*.pc" -print0)
}
compressManPages ()
{
 
    local dir="$1";
    if [ -L "$dir"/share ] || [ -L "$dir"/share/man ] || [ ! -d "$dir/share/man" ]; then
        return;
    fi;
    echo "gzipping man pages under $dir/share/man/";
    find "$dir"/share/man/ -type f -a '!' -regex '.*\.\(bz2\|gz\|xz\)$' -print0 | xargs -0 -n1 -P "$NIX_BUILD_CORES" gzip -n -f;
    find "$dir"/share/man/ -type l -a '!' -regex '.*\.\(bz2\|gz\|xz\)$' -print0 | sort -z | while IFS= read -r -d '' f; do
        local target;
        target="$(readlink -f "$f")";
        if [ -f "$target".gz ]; then
            ln -sf "$target".gz "$f".gz && rm "$f";
        fi;
    done
}
concatStringsSep ()
{
 
    local sep="$1";
    local name="$2";
    local type oldifs;
    if type=$(declare -p "$name" 2> /dev/null); then
        local -n nameref="$name";
        case "${type#* }" in 
            -A*)
                echo "concatStringsSep(): ERROR: trying to use concatStringsSep on an associative array." 1>&2;
                return 1
            ;;
            -a*)
                local IFS="$(printf '\036')"
            ;;
            *)
                local IFS=" "
            ;;
        esac;
        local ifs_separated="${nameref[*]}";
        echo -n "${ifs_separated//"$IFS"/"$sep"}";
    fi
}
concatTo ()
{
 
    local -;
    set -o noglob;
    local -n targetref="$1";
    shift;
    local arg default name type;
    for arg in "$@";
    do
        IFS="=" read -r name default <<< "$arg";
        local -n nameref="$name";
        if [[ -z "${nameref[*]}" && -n "$default" ]]; then
            targetref+=("$default");
        else
            if type=$(declare -p "$name" 2> /dev/null); then
                case "${type#* }" in 
                    -A*)
                        echo "concatTo(): ERROR: trying to use concatTo on an associative array." 1>&2;
                        return 1
                    ;;
                    -a*)
                        targetref+=("${nameref[@]}")
                    ;;
                    *)
                        if [[ "$name" = *"Array" ]]; then
                            nixErrorLog "concatTo(): $name is not declared as array, treating as a singleton. This will become an error in future";
                            targetref+=(${nameref+"${nameref[@]}"});
                        else
                            targetref+=(${nameref-});
                        fi
                    ;;
                esac;
            fi;
        fi;
    done
}
configurePhase ()
{
 
    runHook preConfigure;
    : "${configureScript=}";
    if [[ -z "$configureScript" && -x ./configure ]]; then
        configureScript=./configure;
    fi;
    if [ -z "${dontFixLibtool:-}" ]; then
        export lt_cv_deplibs_check_method="${lt_cv_deplibs_check_method-pass_all}";
        local i;
        find . -iname "ltmain.sh" -print0 | while IFS='' read -r -d '' i; do
            echo "fixing libtool script $i";
            fixLibtool "$i";
        done;
        CONFIGURE_MTIME_REFERENCE=$(mktemp configure.mtime.reference.XXXXXX);
        find . -executable -type f -name configure -exec grep -l 'GNU Libtool is free software; you can redistribute it and/or modify' {} \; -exec touch -r {} "$CONFIGURE_MTIME_REFERENCE" \; -exec sed -i s_/usr/bin/file_file_g {} \; -exec touch -r "$CONFIGURE_MTIME_REFERENCE" {} \;;
        rm -f "$CONFIGURE_MTIME_REFERENCE";
    fi;
    if [[ -z "${dontAddPrefix:-}" && -n "$prefix" ]]; then
        local -r prefixKeyOrDefault="${prefixKey:---prefix=}";
        if [ "${prefixKeyOrDefault: -1}" = " " ]; then
            prependToVar configureFlags "$prefix";
            prependToVar configureFlags "${prefixKeyOrDefault::-1}";
        else
            prependToVar configureFlags "$prefixKeyOrDefault$prefix";
        fi;
    fi;
    if [[ -f "$configureScript" ]]; then
        if [ -z "${dontAddDisableDepTrack:-}" ]; then
            if grep -q dependency-tracking "$configureScript"; then
                prependToVar configureFlags --disable-dependency-tracking;
            fi;
        fi;
        if [ -z "${dontDisableStatic:-}" ]; then
            if grep -q enable-static "$configureScript"; then
                prependToVar configureFlags --disable-static;
            fi;
        fi;
        if [ -z "${dontPatchShebangsInConfigure:-}" ]; then
            patchShebangs --build "$configureScript";
        fi;
    fi;
    if [ -n "$configureScript" ]; then
        local -a flagsArray;
        concatTo flagsArray configureFlags configureFlagsArray;
        echoCmd 'configure flags' "${flagsArray[@]}";
        $configureScript "${flagsArray[@]}";
        unset flagsArray;
    else
        echo "no configure script, doing nothing";
    fi;
    runHook postConfigure
}
consumeEntire ()
{
 
    if IFS='' read -r -d '' "$1"; then
        echo "consumeEntire(): ERROR: Input null bytes, won't process" 1>&2;
        return 1;
    fi
}
definePhases ()
{
 
    if [ -z "${phases[*]:-}" ]; then
        phases="${prePhases[*]:-} unpackPhase patchPhase ${preConfigurePhases[*]:-}             configurePhase ${preBuildPhases[*]:-} buildPhase checkPhase             ${preInstallPhases[*]:-} installPhase ${preFixupPhases[*]:-} fixupPhase installCheckPhase             ${preDistPhases[*]:-} distPhase ${postPhases[*]:-}";
    fi
}
distPhase ()
{
 
    runHook preDist;
    local flagsArray=();
    concatTo flagsArray distFlags distFlagsArray distTarget=dist;
    echo 'dist flags: %q' "${flagsArray[@]}";
    make ${makefile:+-f $makefile} "${flagsArray[@]}";
    if [ "${dontCopyDist:-0}" != 1 ]; then
        mkdir -p "$out/tarballs";
        cp -pvd ${tarballs[*]:-*.tar.gz} "$out/tarballs";
    fi;
    runHook postDist
}
dumpVars ()
{
 
    if [[ "${noDumpEnvVars:-0}" != 1 && -d "$NIX_BUILD_TOP" ]]; then
        local old_umask;
        old_umask=$(umask);
        umask 0077;
        export 2> /dev/null > "$NIX_BUILD_TOP/env-vars";
        umask "$old_umask";
    fi
}
echoCmd ()
{
 
    printf "%s:" "$1";
    shift;
    printf ' %q' "$@";
    echo
}
exitHandler ()
{
 
    exitCode="$?";
    set +e;
    if [ -n "${showBuildStats:-}" ]; then
        read -r -d '' -a buildTimes < <(times);
        echo "build times:";
        echo "user time for the shell             ${buildTimes[0]}";
        echo "system time for the shell           ${buildTimes[1]}";
        echo "user time for all child processes   ${buildTimes[2]}";
        echo "system time for all child processes ${buildTimes[3]}";
    fi;
    if (( "$exitCode" != 0 )); then
        runHook failureHook;
        if [ -n "${succeedOnFailure:-}" ]; then
            echo "build failed with exit code $exitCode (ignored)";
            mkdir -p "$out/nix-support";
            printf "%s" "$exitCode" > "$out/nix-support/failed";
            exit 0;
        fi;
    else
        runHook exitHook;
    fi;
    return "$exitCode"
}
findInputs ()
{
 
    local -r pkg="$1";
    local -r hostOffset="$2";
    local -r targetOffset="$3";
    (( hostOffset <= targetOffset )) || exit 1;
    local varVar="${pkgAccumVarVars[hostOffset + 1]}";
    local varRef="$varVar[$((targetOffset - hostOffset))]";
    local var="${!varRef}";
    unset -v varVar varRef;
    local varSlice="$var[*]";
    case " ${!varSlice-} " in 
        *" $pkg "*)
            return 0
        ;;
    esac;
    unset -v varSlice;
    eval "$var"'+=("$pkg")';
    if ! [ -e "$pkg" ]; then
        echo "build input $pkg does not exist" 1>&2;
        exit 1;
    fi;
    function mapOffset () 
    { 
        local -r inputOffset="$1";
        local -n outputOffset="$2";
        if (( inputOffset <= 0 )); then
            outputOffset=$((inputOffset + hostOffset));
        else
            outputOffset=$((inputOffset - 1 + targetOffset));
        fi
    };
    local relHostOffset;
    for relHostOffset in "${allPlatOffsets[@]}";
    do
        local files="${propagatedDepFilesVars[relHostOffset + 1]}";
        local hostOffsetNext;
        mapOffset "$relHostOffset" hostOffsetNext;
        (( -1 <= hostOffsetNext && hostOffsetNext <= 1 )) || continue;
        local relTargetOffset;
        for relTargetOffset in "${allPlatOffsets[@]}";
        do
            (( "$relHostOffset" <= "$relTargetOffset" )) || continue;
            local fileRef="${files}[$relTargetOffset - $relHostOffset]";
            local file="${!fileRef}";
            unset -v fileRef;
            local targetOffsetNext;
            mapOffset "$relTargetOffset" targetOffsetNext;
            (( -1 <= hostOffsetNext && hostOffsetNext <= 1 )) || continue;
            [[ -f "$pkg/nix-support/$file" ]] || continue;
            local pkgNext;
            read -r -d '' pkgNext < "$pkg/nix-support/$file" || true;
            for pkgNext in $pkgNext;
            do
                findInputs "$pkgNext" "$hostOffsetNext" "$targetOffsetNext";
            done;
        done;
    done
}
fixLibtool ()
{
 
    local search_path;
    for flag in $NIX_LDFLAGS;
    do
        case $flag in 
            -L*)
                search_path+=" ${flag#-L}"
            ;;
        esac;
    done;
    sed -i "$1" -e "s^eval \(sys_lib_search_path=\).*^\1'${search_path:-}'^" -e 's^eval sys_lib_.+search_path=.*^^'
}
fixupPhase ()
{
 
    local output;
    for output in $(getAllOutputNames);
    do
        if [ -e "${!output}" ]; then
            chmod -R u+w,u-s,g-s "${!output}";
        fi;
    done;
    runHook preFixup;
    local output;
    for output in $(getAllOutputNames);
    do
        prefix="${!output}" runHook fixupOutput;
    done;
    recordPropagatedDependencies;
    if [ -n "${setupHook:-}" ]; then
        mkdir -p "${!outputDev}/nix-support";
        substituteAll "$setupHook" "${!outputDev}/nix-support/setup-hook";
    fi;
    if [ -n "${setupHooks:-}" ]; then
        mkdir -p "${!outputDev}/nix-support";
        local hook;
        for hook in ${setupHooks[@]};
        do
            local content;
            consumeEntire content < "$hook";
            substituteAllStream content "file '$hook'" >> "${!outputDev}/nix-support/setup-hook";
            unset -v content;
        done;
        unset -v hook;
    fi;
    if [ -n "${propagatedUserEnvPkgs[*]:-}" ]; then
        mkdir -p "${!outputBin}/nix-support";
        printWords "${propagatedUserEnvPkgs[@]}" > "${!outputBin}/nix-support/propagated-user-env-packages";
    fi;
    runHook postFixup
}
genericBuild ()
{
 
    export GZIP_NO_TIMESTAMPS=1;
    if [ -f "${buildCommandPath:-}" ]; then
        source "$buildCommandPath";
        return;
    fi;
    if [ -n "${buildCommand:-}" ]; then
        eval "$buildCommand";
        return;
    fi;
    definePhases;
    for curPhase in ${phases[*]};
    do
        runPhase "$curPhase";
    done
}
getAllOutputNames ()
{
 
    if [ -n "$__structuredAttrs" ]; then
        echo "${!outputs[*]}";
    else
        echo "$outputs";
    fi
}
getHostRole ()
{
 
    getRole "$hostOffset"
}
getHostRoleEnvHook ()
{
 
    getRole "$depHostOffset"
}
getRole ()
{
 
    case $1 in 
        -1)
            role_post='_FOR_BUILD'
        ;;
        0)
            role_post=''
        ;;
        1)
            role_post='_FOR_TARGET'
        ;;
        *)
            echo "pkg-config-role-hook: used as improper sort of dependency" 1>&2;
            return 1
        ;;
    esac
}
getTargetRole ()
{
 
    getRole "$targetOffset"
}
getTargetRoleEnvHook ()
{
 
    getRole "$depTargetOffset"
}
getTargetRoleWrapper ()
{
 
    case $targetOffset in 
        -1)
            export NIX_PKG_CONFIG_WRAPPER_TARGET_BUILD_x86_64_unknown_linux_gnu=1
        ;;
        0)
            export NIX_PKG_CONFIG_WRAPPER_TARGET_HOST_x86_64_unknown_linux_gnu=1
        ;;
        1)
            export NIX_PKG_CONFIG_WRAPPER_TARGET_TARGET_x86_64_unknown_linux_gnu=1
        ;;
        *)
            echo "pkg-config-role-hook: used as improper sort of dependency" 1>&2;
            return 1
        ;;
    esac
}
gettextDataDirsHook ()
{
 
    getHostRoleEnvHook;
    if [ -d "$1/share/gettext" ]; then
        addToSearchPath "GETTEXTDATADIRS${role_post}" "$1/share/gettext";
    fi
}
glibPostInstallHook ()
{
 
    if [ -d "$prefix/share/glib-2.0/schemas" ]; then
        mkdir -p "${!outputLib}/share/gsettings-schemas/$name/glib-2.0";
        mv "$prefix/share/glib-2.0/schemas" "${!outputLib}/share/gsettings-schemas/$name/glib-2.0/";
    fi;
    addToSearchPath GSETTINGS_SCHEMAS_PATH "${!outputLib}/share/gsettings-schemas/$name"
}
glibPreInstallPhase ()
{
 
    makeFlagsArray+=("gsettingsschemadir=${!outputLib}/share/gsettings-schemas/$name/glib-2.0/schemas/")
}
installCheckPhase ()
{
 
    runHook preInstallCheck;
    if [[ -z "${foundMakefile:-}" ]]; then
        echo "no Makefile or custom installCheckPhase, doing nothing";
    else
        if [[ -z "${installCheckTarget:-}" ]] && ! make -n ${makefile:+-f $makefile} "${installCheckTarget:-installcheck}" > /dev/null 2>&1; then
            echo "no installcheck target in ${makefile:-Makefile}, doing nothing";
        else
            local flagsArray=(${enableParallelChecking:+-j${NIX_BUILD_CORES}} SHELL="$SHELL");
            concatTo flagsArray makeFlags makeFlagsArray installCheckFlags installCheckFlagsArray installCheckTarget=installcheck;
            echoCmd 'installcheck flags' "${flagsArray[@]}";
            make ${makefile:+-f $makefile} "${flagsArray[@]}";
            unset flagsArray;
        fi;
    fi;
    runHook postInstallCheck
}
installPhase ()
{
 
    runHook preInstall;
    if [[ -z "${makeFlags-}" && -z "${makefile:-}" && ! ( -e Makefile || -e makefile || -e GNUmakefile ) ]]; then
        echo "no Makefile or custom installPhase, doing nothing";
        runHook postInstall;
        return;
    else
        foundMakefile=1;
    fi;
    if [ -n "$prefix" ]; then
        mkdir -p "$prefix";
    fi;
    local flagsArray=(${enableParallelInstalling:+-j${NIX_BUILD_CORES}} SHELL="$SHELL");
    concatTo flagsArray makeFlags makeFlagsArray installFlags installFlagsArray installTargets=install;
    echoCmd 'install flags' "${flagsArray[@]}";
    make ${makefile:+-f $makefile} "${flagsArray[@]}";
    unset flagsArray;
    runHook postInstall
}
isELF ()
{
 
    local fn="$1";
    local fd;
    local magic;
    exec {fd}< "$fn";
    LANG=C read -r -n 4 -u "$fd" magic;
    exec {fd}>&-;
    if [ "$magic" = 'ELF' ]; then
        return 0;
    else
        return 1;
    fi
}
isMachO ()
{
 
    local fn="$1";
    local fd;
    local magic;
    exec {fd}< "$fn";
    LANG=C read -r -n 4 -u "$fd" magic;
    exec {fd}>&-;
    if [[ "$magic" = $(echo -ne "\xfe\xed\xfa\xcf") || "$magic" = $(echo -ne "\xcf\xfa\xed\xfe") ]]; then
        return 0;
    else
        if [[ "$magic" = $(echo -ne "\xfe\xed\xfa\xce") || "$magic" = $(echo -ne "\xce\xfa\xed\xfe") ]]; then
            return 0;
        else
            if [[ "$magic" = $(echo -ne "\xca\xfe\xba\xbe") || "$magic" = $(echo -ne "\xbe\xba\xfe\xca") ]]; then
                return 0;
            else
                return 1;
            fi;
        fi;
    fi
}
isScript ()
{
 
    local fn="$1";
    local fd;
    local magic;
    exec {fd}< "$fn";
    LANG=C read -r -n 2 -u "$fd" magic;
    exec {fd}>&-;
    if [[ "$magic" =~ \#! ]]; then
        return 0;
    else
        return 1;
    fi
}
makeCmakeFindLibs ()
{
 
    isystem_seen=;
    iframework_seen=;
    for flag in ${NIX_CFLAGS_COMPILE-} ${NIX_LDFLAGS-};
    do
        if test -n "$isystem_seen" && test -d "$flag"; then
            isystem_seen=;
            addToSearchPath CMAKE_INCLUDE_PATH "${flag}";
        else
            if test -n "$iframework_seen" && test -d "$flag"; then
                iframework_seen=;
                addToSearchPath CMAKE_FRAMEWORK_PATH "${flag}";
            else
                isystem_seen=;
                iframework_seen=;
                case $flag in 
                    -I*)
                        addToSearchPath CMAKE_INCLUDE_PATH "${flag:2}"
                    ;;
                    -L*)
                        addToSearchPath CMAKE_LIBRARY_PATH "${flag:2}"
                    ;;
                    -F*)
                        addToSearchPath CMAKE_FRAMEWORK_PATH "${flag:2}"
                    ;;
                    -isystem)
                        isystem_seen=1
                    ;;
                    -iframework)
                        iframework_seen=1
                    ;;
                esac;
            fi;
        fi;
    done
}
make_glib_find_gsettings_schemas ()
{
 
    for maybe_dir in "$1"/share/gsettings-schemas/*;
    do
        if [[ -d "$maybe_dir/glib-2.0/schemas" ]]; then
            addToSearchPath GSETTINGS_SCHEMAS_PATH "$maybe_dir";
        fi;
    done
}
mapOffset ()
{
 
    local -r inputOffset="$1";
    local -n outputOffset="$2";
    if (( inputOffset <= 0 )); then
        outputOffset=$((inputOffset + hostOffset));
    else
        outputOffset=$((inputOffset - 1 + targetOffset));
    fi
}
moveToOutput ()
{
 
    local patt="$1";
    local dstOut="$2";
    local output;
    for output in $(getAllOutputNames);
    do
        if [ "${!output}" = "$dstOut" ]; then
            continue;
        fi;
        local srcPath;
        for srcPath in "${!output}"/$patt;
        do
            if [ ! -e "$srcPath" ] && [ ! -L "$srcPath" ]; then
                continue;
            fi;
            if [ "$dstOut" = REMOVE ]; then
                echo "Removing $srcPath";
                rm -r "$srcPath";
            else
                local dstPath="$dstOut${srcPath#${!output}}";
                echo "Moving $srcPath to $dstPath";
                if [ -d "$dstPath" ] && [ -d "$srcPath" ]; then
                    rmdir "$srcPath" --ignore-fail-on-non-empty;
                    if [ -d "$srcPath" ]; then
                        mv -t "$dstPath" "$srcPath"/*;
                        rmdir "$srcPath";
                    fi;
                else
                    mkdir -p "$(readlink -m "$dstPath/..")";
                    mv "$srcPath" "$dstPath";
                fi;
            fi;
            local srcParent="$(readlink -m "$srcPath/..")";
            if [ -n "$(find "$srcParent" -maxdepth 0 -type d -empty 2> /dev/null)" ]; then
                echo "Removing empty $srcParent/ and (possibly) its parents";
                rmdir -p --ignore-fail-on-non-empty "$srcParent" 2> /dev/null || true;
            fi;
        done;
    done
}
nixChattyLog ()
{
 
    _nixLogWithLevel 5 "$*"
}
nixDebugLog ()
{
 
    _nixLogWithLevel 6 "$*"
}
nixErrorLog ()
{
 
    _nixLogWithLevel 0 "$*"
}
nixInfoLog ()
{
 
    _nixLogWithLevel 3 "$*"
}
nixLog ()
{
 
    [[ -z ${NIX_LOG_FD-} ]] && return 0;
    local callerName="${FUNCNAME[1]}";
    if [[ $callerName == "_callImplicitHook" ]]; then
        callerName="${hookName:?}";
    fi;
    printf "%s: %s\n" "$callerName" "$*" >&"$NIX_LOG_FD"
}
nixNoticeLog ()
{
 
    _nixLogWithLevel 2 "$*"
}
nixTalkativeLog ()
{
 
    _nixLogWithLevel 4 "$*"
}
nixVomitLog ()
{
 
    _nixLogWithLevel 7 "$*"
}
nixWarnLog ()
{
 
    _nixLogWithLevel 1 "$*"
}
noBrokenSymlinks ()
{
 
    local -r output="${1:?}";
    local path;
    local pathParent;
    local symlinkTarget;
    local -i numDanglingSymlinks=0;
    local -i numReflexiveSymlinks=0;
    local -i numUnreadableSymlinks=0;
    if [[ ! -e $output ]]; then
        nixWarnLog "skipping non-existent output $output";
        return 0;
    fi;
    nixInfoLog "running on $output";
    while IFS= read -r -d '' path; do
        pathParent="$(dirname "$path")";
        if ! symlinkTarget="$(readlink "$path")"; then
            nixErrorLog "the symlink $path is unreadable";
            numUnreadableSymlinks+=1;
            continue;
        fi;
        if [[ $symlinkTarget == /* ]]; then
            nixInfoLog "symlink $path points to absolute target $symlinkTarget";
        else
            nixInfoLog "symlink $path points to relative target $symlinkTarget";
            symlinkTarget="$(realpath --no-symlinks --canonicalize-missing "$pathParent/$symlinkTarget")";
        fi;
        if [[ $symlinkTarget = "$TMPDIR"/* ]]; then
            nixErrorLog "the symlink $path points to $TMPDIR directory: $symlinkTarget";
            numDanglingSymlinks+=1;
            continue;
        fi;
        if [[ $symlinkTarget != "$NIX_STORE"/* ]]; then
            nixInfoLog "symlink $path points outside the Nix store; ignoring";
            continue;
        fi;
        if [[ $path == "$symlinkTarget" ]]; then
            nixErrorLog "the symlink $path is reflexive";
            numReflexiveSymlinks+=1;
        else
            if [[ ! -e $symlinkTarget ]]; then
                nixErrorLog "the symlink $path points to a missing target: $symlinkTarget";
                numDanglingSymlinks+=1;
            else
                nixDebugLog "the symlink $path is irreflexive and points to a target which exists";
            fi;
        fi;
    done < <(find "$output" -type l -print0);
    if ((numDanglingSymlinks > 0 || numReflexiveSymlinks > 0 || numUnreadableSymlinks > 0)); then
        nixErrorLog "found $numDanglingSymlinks dangling symlinks, $numReflexiveSymlinks reflexive symlinks and $numUnreadableSymlinks unreadable symlinks";
        exit 1;
    fi;
    return 0
}
noBrokenSymlinksInAllOutputs ()
{
 
    if [[ -z ${dontCheckForBrokenSymlinks-} ]]; then
        for output in $(getAllOutputNames);
        do
            noBrokenSymlinks "${!output}";
        done;
    fi
}
patchELF ()
{
 
    local dir="$1";
    [ -e "$dir" ] || return 0;
    echo "shrinking RPATHs of ELF executables and libraries in $dir";
    local i;
    while IFS= read -r -d '' i; do
        if [[ "$i" =~ .build-id ]]; then
            continue;
        fi;
        if ! isELF "$i"; then
            continue;
        fi;
        echo "shrinking $i";
        patchelf --shrink-rpath "$i" || true;
    done < <(find "$dir" -type f -print0)
}
patchPhase ()
{
 
    runHook prePatch;
    local -a patchesArray;
    concatTo patchesArray patches;
    local -a flagsArray;
    concatTo flagsArray patchFlags=-p1;
    for i in "${patchesArray[@]}";
    do
        echo "applying patch $i";
        local uncompress=cat;
        case "$i" in 
            *.gz)
                uncompress="gzip -d"
            ;;
            *.bz2)
                uncompress="bzip2 -d"
            ;;
            *.xz)
                uncompress="xz -d"
            ;;
            *.lzma)
                uncompress="lzma -d"
            ;;
        esac;
        $uncompress < "$i" 2>&1 | patch "${flagsArray[@]}";
    done;
    runHook postPatch
}
patchShebangs ()
{
 
    local pathName;
    local update=false;
    while [[ $# -gt 0 ]]; do
        case "$1" in 
            --host)
                pathName=HOST_PATH;
                shift
            ;;
            --build)
                pathName=PATH;
                shift
            ;;
            --update)
                update=true;
                shift
            ;;
            --)
                shift;
                break
            ;;
            -* | --*)
                echo "Unknown option $1 supplied to patchShebangs" 1>&2;
                return 1
            ;;
            *)
                break
            ;;
        esac;
    done;
    echo "patching script interpreter paths in $@";
    local f;
    local oldPath;
    local newPath;
    local arg0;
    local args;
    local oldInterpreterLine;
    local newInterpreterLine;
    if [[ $# -eq 0 ]]; then
        echo "No arguments supplied to patchShebangs" 1>&2;
        return 0;
    fi;
    local f;
    while IFS= read -r -d '' f; do
        isScript "$f" || continue;
        read -r oldInterpreterLine < "$f" || [ "$oldInterpreterLine" ];
        read -r oldPath arg0 args <<< "${oldInterpreterLine:2}";
        if [[ -z "${pathName:-}" ]]; then
            if [[ -n $strictDeps && $f == "$NIX_STORE"* ]]; then
                pathName=HOST_PATH;
            else
                pathName=PATH;
            fi;
        fi;
        if [[ "$oldPath" == *"/bin/env" ]]; then
            if [[ $arg0 == "-S" ]]; then
                arg0=${args%% *};
                [[ "$args" == *" "* ]] && args=${args#* } || args=;
                newPath="$(PATH="${!pathName}" type -P "env" || true)";
                args="-S $(PATH="${!pathName}" type -P "$arg0" || true) $args";
            else
                if [[ $arg0 == "-"* || $arg0 == *"="* ]]; then
                    echo "$f: unsupported interpreter directive \"$oldInterpreterLine\" (set dontPatchShebangs=1 and handle shebang patching yourself)" 1>&2;
                    exit 1;
                else
                    newPath="$(PATH="${!pathName}" type -P "$arg0" || true)";
                fi;
            fi;
        else
            if [[ -z $oldPath ]]; then
                oldPath="/bin/sh";
            fi;
            newPath="$(PATH="${!pathName}" type -P "$(basename "$oldPath")" || true)";
            args="$arg0 $args";
        fi;
        newInterpreterLine="$newPath $args";
        newInterpreterLine=${newInterpreterLine%${newInterpreterLine##*[![:space:]]}};
        if [[ -n "$oldPath" && ( "$update" == true || "${oldPath:0:${#NIX_STORE}}" != "$NIX_STORE" ) ]]; then
            if [[ -n "$newPath" && "$newPath" != "$oldPath" ]]; then
                echo "$f: interpreter directive changed from \"$oldInterpreterLine\" to \"$newInterpreterLine\"";
                escapedInterpreterLine=${newInterpreterLine//\\/\\\\};
                timestamp=$(stat --printf "%y" "$f");
                tmpFile=$(mktemp -t patchShebangs.XXXXXXXXXX);
                sed -e "1 s|.*|#\!$escapedInterpreterLine|" "$f" > "$tmpFile";
                local restoreReadOnly;
                if [[ ! -w "$f" ]]; then
                    chmod +w "$f";
                    restoreReadOnly=true;
                fi;
                cat "$tmpFile" > "$f";
                rm "$tmpFile";
                if [[ -n "${restoreReadOnly:-}" ]]; then
                    chmod -w "$f";
                fi;
                touch --date "$timestamp" "$f";
            fi;
        fi;
    done < <(find "$@" -type f -perm -0100 -print0)
}
patchShebangsAuto ()
{
 
    if [[ -z "${dontPatchShebangs-}" && -e "$prefix" ]]; then
        if [[ "$output" != out && "$output" = "$outputDev" ]]; then
            patchShebangs --build "$prefix";
        else
            patchShebangs --host "$prefix";
        fi;
    fi
}
pkgConfigWrapper_addPkgConfigPath ()
{
 
    local role_post;
    getHostRoleEnvHook;
    addToSearchPath "PKG_CONFIG_PATH${role_post}" "$1/lib/pkgconfig";
    addToSearchPath "PKG_CONFIG_PATH${role_post}" "$1/share/pkgconfig"
}
prependToVar ()
{
 
    local -n nameref="$1";
    local useArray type;
    if [ -n "$__structuredAttrs" ]; then
        useArray=true;
    else
        useArray=false;
    fi;
    if type=$(declare -p "$1" 2> /dev/null); then
        case "${type#* }" in 
            -A*)
                echo "prependToVar(): ERROR: trying to use prependToVar on an associative array." 1>&2;
                return 1
            ;;
            -a*)
                useArray=true
            ;;
            *)
                useArray=false
            ;;
        esac;
    fi;
    shift;
    if $useArray; then
        nameref=("$@" ${nameref+"${nameref[@]}"});
    else
        nameref="$* ${nameref-}";
    fi
}
printLines ()
{
 
    (( "$#" > 0 )) || return 0;
    printf '%s\n' "$@"
}
printPhases ()
{
 
    definePhases;
    local phase;
    for phase in ${phases[*]};
    do
        printf '%s\n' "$phase";
    done
}
printWords ()
{
 
    (( "$#" > 0 )) || return 0;
    printf '%s ' "$@"
}
recordPropagatedDependencies ()
{
 
    declare -ra flatVars=(depsBuildBuildPropagated propagatedNativeBuildInputs depsBuildTargetPropagated depsHostHostPropagated propagatedBuildInputs depsTargetTargetPropagated);
    declare -ra flatFiles=("${propagatedBuildDepFiles[@]}" "${propagatedHostDepFiles[@]}" "${propagatedTargetDepFiles[@]}");
    local propagatedInputsIndex;
    for propagatedInputsIndex in "${!flatVars[@]}";
    do
        local propagatedInputsSlice="${flatVars[$propagatedInputsIndex]}[@]";
        local propagatedInputsFile="${flatFiles[$propagatedInputsIndex]}";
        [[ -n "${!propagatedInputsSlice}" ]] || continue;
        mkdir -p "${!outputDev}/nix-support";
        printWords ${!propagatedInputsSlice} > "${!outputDev}/nix-support/$propagatedInputsFile";
    done
}
runHook ()
{
 
    local hookName="$1";
    shift;
    local hooksSlice="${hookName%Hook}Hooks[@]";
    local hook;
    for hook in "_callImplicitHook 0 $hookName" ${!hooksSlice+"${!hooksSlice}"};
    do
        _logHook "$hookName" "$hook" "$@";
        _eval "$hook" "$@";
    done;
    return 0
}
runOneHook ()
{
 
    local hookName="$1";
    shift;
    local hooksSlice="${hookName%Hook}Hooks[@]";
    local hook ret=1;
    for hook in "_callImplicitHook 1 $hookName" ${!hooksSlice+"${!hooksSlice}"};
    do
        _logHook "$hookName" "$hook" "$@";
        if _eval "$hook" "$@"; then
            ret=0;
            break;
        fi;
    done;
    return "$ret"
}
runPhase ()
{
 
    local curPhase="$*";
    if [[ "$curPhase" = unpackPhase && -n "${dontUnpack:-}" ]]; then
        return;
    fi;
    if [[ "$curPhase" = patchPhase && -n "${dontPatch:-}" ]]; then
        return;
    fi;
    if [[ "$curPhase" = configurePhase && -n "${dontConfigure:-}" ]]; then
        return;
    fi;
    if [[ "$curPhase" = buildPhase && -n "${dontBuild:-}" ]]; then
        return;
    fi;
    if [[ "$curPhase" = checkPhase && -z "${doCheck:-}" ]]; then
        return;
    fi;
    if [[ "$curPhase" = installPhase && -n "${dontInstall:-}" ]]; then
        return;
    fi;
    if [[ "$curPhase" = fixupPhase && -n "${dontFixup:-}" ]]; then
        return;
    fi;
    if [[ "$curPhase" = installCheckPhase && -z "${doInstallCheck:-}" ]]; then
        return;
    fi;
    if [[ "$curPhase" = distPhase && -z "${doDist:-}" ]]; then
        return;
    fi;
    showPhaseHeader "$curPhase";
    dumpVars;
    local startTime endTime;
    startTime=$(date +"%s");
    eval "${!curPhase:-$curPhase}";
    endTime=$(date +"%s");
    showPhaseFooter "$curPhase" "$startTime" "$endTime";
    if [ "$curPhase" = unpackPhase ]; then
        [ -n "${sourceRoot:-}" ] && chmod +x -- "${sourceRoot}";
        cd -- "${sourceRoot:-.}";
    fi
}
showPhaseFooter ()
{
 
    local phase="$1";
    local startTime="$2";
    local endTime="$3";
    local delta=$(( endTime - startTime ));
    (( delta < 30 )) && return;
    local H=$((delta/3600));
    local M=$((delta%3600/60));
    local S=$((delta%60));
    echo -n "$phase completed in ";
    (( H > 0 )) && echo -n "$H hours ";
    (( M > 0 )) && echo -n "$M minutes ";
    echo "$S seconds"
}
showPhaseHeader ()
{
 
    local phase="$1";
    echo "Running phase: $phase";
    if [[ -z ${NIX_LOG_FD-} ]]; then
        return;
    fi;
    printf "@nix { \"action\": \"setPhase\", \"phase\": \"%s\" }\n" "$phase" >&"$NIX_LOG_FD"
}
stripDirs ()
{
 
    local cmd="$1";
    local ranlibCmd="$2";
    local paths="$3";
    local stripFlags="$4";
    local excludeFlags=();
    local pathsNew=;
    [ -z "$cmd" ] && echo "stripDirs: Strip command is empty" 1>&2 && exit 1;
    [ -z "$ranlibCmd" ] && echo "stripDirs: Ranlib command is empty" 1>&2 && exit 1;
    local pattern;
    if [ -n "${stripExclude:-}" ]; then
        for pattern in "${stripExclude[@]}";
        do
            excludeFlags+=(-a '!' '(' -name "$pattern" -o -wholename "$prefix/$pattern" ')');
        done;
    fi;
    local p;
    for p in ${paths};
    do
        if [ -e "$prefix/$p" ]; then
            pathsNew="${pathsNew} $prefix/$p";
        fi;
    done;
    paths=${pathsNew};
    if [ -n "${paths}" ]; then
        echo "stripping (with command $cmd and flags $stripFlags) in $paths";
        local striperr;
        striperr="$(mktemp --tmpdir="$TMPDIR" 'striperr.XXXXXX')";
        find $paths -type f "${excludeFlags[@]}" -a '!' -path "$prefix/lib/debug/*" -printf '%D-%i,%p\0' | sort -t, -k1,1 -u -z | cut -d, -f2- -z | xargs -r -0 -n1 -P "$NIX_BUILD_CORES" -- $cmd $stripFlags 2> "$striperr" || exit_code=$?;
        [[ "$exit_code" = 123 || -z "$exit_code" ]] || ( cat "$striperr" 1>&2 && exit 1 );
        rm "$striperr";
        find $paths -name '*.a' -type f -exec $ranlibCmd '{}' \; 2> /dev/null;
    fi
}
stripHash ()
{
 
    local strippedName casematchOpt=0;
    strippedName="$(basename -- "$1")";
    shopt -q nocasematch && casematchOpt=1;
    shopt -u nocasematch;
    if [[ "$strippedName" =~ ^[a-z0-9]{32}- ]]; then
        echo "${strippedName:33}";
    else
        echo "$strippedName";
    fi;
    if (( casematchOpt )); then
        shopt -s nocasematch;
    fi
}
substitute ()
{
 
    local input="$1";
    local output="$2";
    shift 2;
    if [ ! -f "$input" ]; then
        echo "substitute(): ERROR: file '$input' does not exist" 1>&2;
        return 1;
    fi;
    local content;
    consumeEntire content < "$input";
    if [ -e "$output" ]; then
        chmod +w "$output";
    fi;
    substituteStream content "file '$input'" "$@" > "$output"
}
substituteAll ()
{
 
    local input="$1";
    local output="$2";
    local -a args=();
    _allFlags;
    substitute "$input" "$output" "${args[@]}"
}
substituteAllInPlace ()
{
 
    local fileName="$1";
    shift;
    substituteAll "$fileName" "$fileName" "$@"
}
substituteAllStream ()
{
 
    local -a args=();
    _allFlags;
    substituteStream "$1" "$2" "${args[@]}"
}
substituteInPlace ()
{
 
    local -a fileNames=();
    for arg in "$@";
    do
        if [[ "$arg" = "--"* ]]; then
            break;
        fi;
        fileNames+=("$arg");
        shift;
    done;
    if ! [[ "${#fileNames[@]}" -gt 0 ]]; then
        echo "substituteInPlace called without any files to operate on (files must come before options!)" 1>&2;
        return 1;
    fi;
    for file in "${fileNames[@]}";
    do
        substitute "$file" "$file" "$@";
    done
}
substituteStream ()
{
 
    local var=$1;
    local description=$2;
    shift 2;
    while (( "$#" )); do
        local replace_mode="$1";
        case "$1" in 
            --replace)
                if ! "$_substituteStream_has_warned_replace_deprecation"; then
                    echo "substituteStream() in derivation $name: WARNING: '--replace' is deprecated, use --replace-{fail,warn,quiet}. ($description)" 1>&2;
                    _substituteStream_has_warned_replace_deprecation=true;
                fi;
                replace_mode='--replace-warn'
            ;&
            --replace-quiet | --replace-warn | --replace-fail)
                pattern="$2";
                replacement="$3";
                shift 3;
                if ! [[ "${!var}" == *"$pattern"* ]]; then
                    if [ "$replace_mode" == --replace-warn ]; then
                        printf "substituteStream() in derivation $name: WARNING: pattern %q doesn't match anything in %s\n" "$pattern" "$description" 1>&2;
                    else
                        if [ "$replace_mode" == --replace-fail ]; then
                            printf "substituteStream() in derivation $name: ERROR: pattern %q doesn't match anything in %s\n" "$pattern" "$description" 1>&2;
                            return 1;
                        fi;
                    fi;
                fi;
                eval "$var"'=${'"$var"'//"$pattern"/"$replacement"}'
            ;;
            --subst-var)
                local varName="$2";
                shift 2;
                if ! [[ "$varName" =~ ^[a-zA-Z_][a-zA-Z0-9_]*$ ]]; then
                    echo "substituteStream() in derivation $name: ERROR: substitution variables must be valid Bash names, \"$varName\" isn't." 1>&2;
                    return 1;
                fi;
                if [ -z ${!varName+x} ]; then
                    echo "substituteStream() in derivation $name: ERROR: variable \$$varName is unset" 1>&2;
                    return 1;
                fi;
                pattern="@$varName@";
                replacement="${!varName}";
                eval "$var"'=${'"$var"'//"$pattern"/"$replacement"}'
            ;;
            --subst-var-by)
                pattern="@$2@";
                replacement="$3";
                eval "$var"'=${'"$var"'//"$pattern"/"$replacement"}';
                shift 3
            ;;
            *)
                echo "substituteStream() in derivation $name: ERROR: Invalid command line argument: $1" 1>&2;
                return 1
            ;;
        esac;
    done;
    printf "%s" "${!var}"
}
sysconfigdataHook ()
{
 
    if [ "$1" = '/nix/store/0r6k8xa2kgqyp3r4v2w7yrb80ma2iawm-python3-3.13.12' ]; then
        export _PYTHON_HOST_PLATFORM='linux-x86_64';
        export _PYTHON_SYSCONFIGDATA_NAME='_sysconfigdata__linux_x86_64-linux-gnu';
    fi
}
toPythonPath ()
{
 
    local paths="$1";
    local result=;
    for i in $paths;
    do
        p="$i/lib/python3.13/site-packages";
        result="${result}${result:+:}$p";
    done;
    echo $result
}
unpackFile ()
{
 
    curSrc="$1";
    echo "unpacking source archive $curSrc";
    if ! runOneHook unpackCmd "$curSrc"; then
        echo "do not know how to unpack source archive $curSrc";
        exit 1;
    fi
}
unpackPhase ()
{
 
    runHook preUnpack;
    if [ -z "${srcs:-}" ]; then
        if [ -z "${src:-}" ]; then
            echo 'variable $src or $srcs should point to the source';
            exit 1;
        fi;
        srcs="$src";
    fi;
    local -a srcsArray;
    concatTo srcsArray srcs;
    local dirsBefore="";
    for i in *;
    do
        if [ -d "$i" ]; then
            dirsBefore="$dirsBefore $i ";
        fi;
    done;
    for i in "${srcsArray[@]}";
    do
        unpackFile "$i";
    done;
    : "${sourceRoot=}";
    if [ -n "${setSourceRoot:-}" ]; then
        runOneHook setSourceRoot;
    else
        if [ -z "$sourceRoot" ]; then
            for i in *;
            do
                if [ -d "$i" ]; then
                    case $dirsBefore in 
                        *\ $i\ *)

                        ;;
                        *)
                            if [ -n "$sourceRoot" ]; then
                                echo "unpacker produced multiple directories";
                                exit 1;
                            fi;
                            sourceRoot="$i"
                        ;;
                    esac;
                fi;
            done;
        fi;
    fi;
    if [ -z "$sourceRoot" ]; then
        echo "unpacker appears to have produced no directories";
        exit 1;
    fi;
    echo "source root is $sourceRoot";
    if [ "${dontMakeSourcesWritable:-0}" != 1 ]; then
        chmod -R u+w -- "$sourceRoot";
    fi;
    runHook postUnpack
}
updateAutotoolsGnuConfigScriptsPhase ()
{
 
    if [ -n "${dontUpdateAutotoolsGnuConfigScripts-}" ]; then
        return;
    fi;
    for script in config.sub config.guess;
    do
        for f in $(find . -type f -name "$script");
        do
            echo "Updating Autotools / GNU config script to a newer upstream version: $f";
            cp -f "/nix/store/kppfbp4x7mhfz1q5zswavxxxq71v2f7c-gnu-config-2024-01-01/$script" "$f";
        done;
    done
}
updateSourceDateEpoch ()
{
 
    local path="$1";
    [[ $path == -* ]] && path="./$path";
    local -a res=($(find "$path" -type f -not -newer "$NIX_BUILD_TOP/.." -printf '%T@ "%p"\0' | sort -n --zero-terminated | tail -n1 --zero-terminated | head -c -1));
    local time="${res[0]//\.[0-9]*/}";
    local newestFile="${res[1]}";
    if [ "${time:-0}" -gt "$SOURCE_DATE_EPOCH" ]; then
        echo "setting SOURCE_DATE_EPOCH to timestamp $time of file $newestFile";
        export SOURCE_DATE_EPOCH="$time";
        local now="$(date +%s)";
        if [ "$time" -gt $((now - 60)) ]; then
            echo "warning: file $newestFile may be generated; SOURCE_DATE_EPOCH may be non-deterministic";
        fi;
    fi
}
PATH="$PATH${nix_saved_PATH:+:$nix_saved_PATH}"
XDG_DATA_DIRS="$XDG_DATA_DIRS${nix_saved_XDG_DATA_DIRS:+:$nix_saved_XDG_DATA_DIRS}"
export NIX_BUILD_TOP="$(mktemp -d -t nix-shell.XXXXXX)"
export TMP="$NIX_BUILD_TOP"
export TMPDIR="$NIX_BUILD_TOP"
export TEMP="$NIX_BUILD_TOP"
export TEMPDIR="$NIX_BUILD_TOP"
eval "${shellHook:-}"


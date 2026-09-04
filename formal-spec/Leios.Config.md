## Leios.Config

This module defines the configuration parameters for the Leios protocol.
It includes block type definitions (Input Blocks, Endorser Blocks, Votes)
and protocol parameters such as party counts, stake distribution,
stage length, and winning slot specifications.
<!--
<pre class="Agda"><a id="291" class="Symbol">{-#</a> <a id="295" class="Keyword">OPTIONS</a> <a id="303" class="Pragma">--safe</a> <a id="310" class="Symbol">#-}</a>
</pre>-->
<pre class="Agda"><a id="330" class="Keyword">open</a> <a id="335" class="Keyword">import</a> <a id="342" href="Leios.Prelude.html" class="Module">Leios.Prelude</a>
<a id="356" class="Keyword">open</a> <a id="361" class="Keyword">import</a> <a id="368" href="Tactic.Defaults.html" class="Module">Tactic.Defaults</a>
<a id="384" class="Keyword">open</a> <a id="389" class="Keyword">import</a> <a id="396" href="Tactic.Derive.DecEq.html" class="Module">Tactic.Derive.DecEq</a>

<a id="417" class="Keyword">module</a> <a id="424" href="Leios.Config.html" class="Module">Leios.Config</a> <a id="437" class="Keyword">where</a>

<a id="444" class="Keyword">data</a> <a id="BlockType"></a><a id="449" href="Leios.Config.html#449" class="Datatype">BlockType</a> <a id="459" class="Symbol">:</a> <a id="461" href="Agda.Primitive.html#388" class="Primitive">Type</a> <a id="466" class="Keyword">where</a>
  <a id="BlockType.IB"></a><a id="474" href="Leios.Config.html#474" class="InductiveConstructor">IB</a> <a id="BlockType.EB"></a><a id="477" href="Leios.Config.html#477" class="InductiveConstructor">EB</a> <a id="BlockType.VT"></a><a id="480" href="Leios.Config.html#480" class="InductiveConstructor">VT</a> <a id="483" class="Symbol">:</a> <a id="485" href="Leios.Config.html#449" class="Datatype">BlockType</a>

<a id="496" class="Keyword">unquoteDecl</a> <a id="DecEq-BlockType"></a><a id="508" href="Leios.Config.html#508" class="Function">DecEq-BlockType</a> <a id="524" class="Symbol">=</a> <a id="526" href="Tactic.Derive.DecEq.html#5150" class="Function">derive-DecEq</a> <a id="539" class="Symbol">((</a><a id="541" class="Keyword">quote</a> <a id="547" href="Leios.Config.html#449" class="Datatype">BlockType</a> <a id="557" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="559" href="Leios.Config.html#508" class="Function">DecEq-BlockType</a><a id="574" class="Symbol">)</a> <a id="576" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="578" href="Agda.Builtin.List.html#184" class="InductiveConstructor">[]</a><a id="580" class="Symbol">)</a>

<a id="583" class="Keyword">record</a> <a id="NetworkParams"></a><a id="590" href="Leios.Config.html#590" class="Record">NetworkParams</a> <a id="604" class="Symbol">:</a> <a id="606" href="Agda.Primitive.html#388" class="Primitive">Type</a> <a id="611" class="Keyword">where</a>
  <a id="619" class="Keyword">field</a> <a id="NetworkParams.numberOfParties"></a><a id="625" href="Leios.Config.html#625" class="Field">numberOfParties</a>   <a id="643" class="Symbol">:</a> <a id="645" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
        <a id="NetworkParams.stakeDistribution"></a><a id="655" href="Leios.Config.html#655" class="Field">stakeDistribution</a> <a id="673" class="Symbol">:</a> <a id="675" href="Axiom.Set.TotalMap.html#574" class="Record">TotalMap</a> <a id="684" class="Symbol">(</a><a id="685" href="Data.Fin.Base.html#1132" class="Datatype">Fin</a> <a id="689" href="Leios.Config.html#625" class="Field">numberOfParties</a><a id="704" class="Symbol">)</a> <a id="706" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
        <a id="716" class="Symbol">⦃</a> <a id="NetworkParams.NonZero-numberOfParties"></a><a id="718" href="Leios.Config.html#718" class="Field">NonZero-numberOfParties</a> <a id="742" class="Symbol">⦄</a> <a id="744" class="Symbol">:</a> <a id="746" href="Data.Nat.Base.html#3266" class="Record">NonZero</a> <a id="754" href="Leios.Config.html#625" class="Field">numberOfParties</a>

<a id="771" class="Keyword">record</a> <a id="Params"></a><a id="778" href="Leios.Config.html#778" class="Record">Params</a> <a id="785" class="Symbol">:</a> <a id="787" href="Agda.Primitive.html#388" class="Primitive">Type</a> <a id="792" class="Keyword">where</a>
  <a id="800" class="Keyword">field</a> <a id="Params.networkParams"></a><a id="806" href="Leios.Config.html#806" class="Field">networkParams</a>    <a id="823" class="Symbol">:</a> <a id="825" href="Leios.Config.html#590" class="Record">NetworkParams</a>
        <a id="Params.Lhdr"></a><a id="847" href="Leios.Config.html#847" class="Field">Lhdr</a> <a id="Params.Lvote"></a><a id="852" href="Leios.Config.html#852" class="Field">Lvote</a> <a id="Params.Ldiff"></a><a id="858" href="Leios.Config.html#858" class="Field">Ldiff</a> <a id="864" class="Symbol">:</a> <a id="866" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
        <a id="876" class="Comment">-- stake coverage σc, as a ratio σc-num / σc-den</a>
        <a id="Params.σc-num"></a><a id="933" href="Leios.Config.html#933" class="Field">σc-num</a> <a id="Params.σc-den"></a><a id="940" href="Leios.Config.html#940" class="Field">σc-den</a>    <a id="950" class="Symbol">:</a> <a id="952" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>

  <a id="957" class="Keyword">open</a> <a id="962" href="Leios.Config.html#590" class="Module">NetworkParams</a> <a id="976" href="Leios.Config.html#806" class="Field">networkParams</a> <a id="990" class="Keyword">public</a>

<a id="998" class="Keyword">module</a> <a id="1005" href="Leios.Config.html#1005" class="Module">_</a> <a id="1007" class="Symbol">(</a><a id="1008" href="Leios.Config.html#1008" class="Bound">params</a> <a id="1015" class="Symbol">:</a> <a id="1017" href="Leios.Config.html#778" class="Record">Params</a><a id="1023" class="Symbol">)</a> <a id="1025" class="Keyword">where</a>
  <a id="1033" class="Keyword">open</a> <a id="1038" href="Leios.Config.html#778" class="Module">Params</a> <a id="1045" href="Leios.Config.html#1008" class="Bound">params</a>

  <a id="1055" class="Keyword">private</a>
    <a id="1067" href="Leios.Config.html#1067" class="Function">allStakes</a> <a id="1077" class="Symbol">:</a> <a id="1079" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="1084" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
    <a id="1090" href="Leios.Config.html#1067" class="Function">allStakes</a> <a id="1100" class="Symbol">=</a> <a id="1102" href="Data.List.Base.html#6139" class="Function">L.tabulate</a> <a id="1113" class="Symbol">(</a><a id="1114" href="Axiom.Set.TotalMap.html#779" class="Function">TotalMap.lookup</a> <a id="1130" href="Leios.Config.html#655" class="Function">stakeDistribution</a><a id="1147" class="Symbol">)</a>

    <a id="1154" href="Leios.Config.html#1154" class="Function">totalStake</a> <a id="1165" class="Symbol">:</a> <a id="1167" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
    <a id="1173" href="Leios.Config.html#1154" class="Function">totalStake</a> <a id="1184" class="Symbol">=</a> <a id="1186" href="Data.List.Base.html#17278" class="Function">L.sum</a> <a id="1192" href="Leios.Config.html#1067" class="Function">allStakes</a>

    <a id="1207" class="Comment">-- stake held by pools with strictly more stake than the given one</a>
    <a id="1278" href="Leios.Config.html#1278" class="Function">richerStake</a> <a id="1290" class="Symbol">:</a> <a id="1292" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1294" class="Symbol">→</a> <a id="1296" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
    <a id="1302" href="Leios.Config.html#1278" class="Function">richerStake</a> <a id="1314" href="Leios.Config.html#1314" class="Bound">st</a> <a id="1317" class="Symbol">=</a> <a id="1319" href="Data.List.Base.html#17278" class="Function">L.sum</a> <a id="1325" class="Symbol">(</a><a id="1326" href="Data.List.Base.html#10389" class="Function">L.filter</a> <a id="1335" class="Symbol">(</a><a id="1336" href="Leios.Config.html#1314" class="Bound">st</a> <a id="1339" href="Class.HasOrder.Core.html#1076" class="Function Operator">&lt;?_</a><a id="1342" class="Symbol">)</a> <a id="1344" href="Leios.Config.html#1067" class="Function">allStakes</a><a id="1353" class="Symbol">)</a>
</pre>Voting-committee membership by stake-based truncation: order pools by
stake descending and accumulate until the cumulative stake covers the σc
target; the committee is fixed for the whole epoch. A pool with stake `st`
is on the committee iff the pools with strictly more stake do not already
cover the target. Pools of equal stake at the boundary are all included.
<pre class="Agda">  <a id="1734" href="Leios.Config.html#1734" class="Function">inVotingCommittee</a> <a id="1752" class="Symbol">:</a> <a id="1754" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1756" class="Symbol">→</a> <a id="1758" href="Agda.Primitive.html#388" class="Primitive">Type</a>
  <a id="1765" href="Leios.Config.html#1734" class="Function">inVotingCommittee</a> <a id="1783" href="Leios.Config.html#1783" class="Bound">st</a> <a id="1786" class="Symbol">=</a> <a id="1788" href="Leios.Config.html#1278" class="Function">richerStake</a> <a id="1800" href="Leios.Config.html#1783" class="Bound">st</a> <a id="1803" href="Agda.Builtin.Nat.html#539" class="Primitive Operator">*</a> <a id="1805" href="Leios.Config.html#940" class="Field">σc-den</a> <a id="1812" href="Class.HasOrder.Core.html#646" class="Field Operator">&lt;</a> <a id="1814" href="Leios.Config.html#1154" class="Function">totalStake</a> <a id="1825" href="Agda.Builtin.Nat.html#539" class="Primitive Operator">*</a> <a id="1827" href="Leios.Config.html#933" class="Field">σc-num</a>

<a id="1835" class="Keyword">record</a> <a id="TestParams"></a><a id="1842" href="Leios.Config.html#1842" class="Record">TestParams</a> <a id="1853" class="Symbol">(</a><a id="1854" href="Leios.Config.html#1854" class="Bound">params</a> <a id="1861" class="Symbol">:</a> <a id="1863" href="Leios.Config.html#778" class="Record">Params</a><a id="1869" class="Symbol">)</a> <a id="1871" class="Symbol">:</a> <a id="1873" href="Agda.Primitive.html#388" class="Primitive">Type</a> <a id="1878" class="Keyword">where</a>
  <a id="1886" class="Keyword">open</a> <a id="1891" href="Leios.Config.html#778" class="Module">Params</a> <a id="1898" href="Leios.Config.html#1854" class="Bound">params</a>

  <a id="1908" class="Keyword">field</a> <a id="TestParams.sutId"></a><a id="1914" href="Leios.Config.html#1914" class="Field">sutId</a> <a id="1920" class="Symbol">:</a> <a id="1922" href="Data.Fin.Base.html#1132" class="Datatype">Fin</a> <a id="1926" href="Leios.Config.html#625" class="Function">numberOfParties</a>
        <a id="TestParams.winning-slots"></a><a id="1950" href="Leios.Config.html#1950" class="Field">winning-slots</a> <a id="1964" class="Symbol">:</a> <a id="1966" href="abstract-set-theory.FiniteSetTheory.html#488" class="Function Operator">ℙ</a> <a id="1968" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
</pre>
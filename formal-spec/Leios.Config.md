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
  <a id="800" class="Keyword">field</a> <a id="Params.networkParams"></a><a id="806" href="Leios.Config.html#806" class="Field">networkParams</a> <a id="820" class="Symbol">:</a> <a id="822" href="Leios.Config.html#590" class="Record">NetworkParams</a>

  <a id="839" class="Keyword">open</a> <a id="844" href="Leios.Config.html#590" class="Module">NetworkParams</a> <a id="858" href="Leios.Config.html#806" class="Field">networkParams</a> <a id="872" class="Keyword">public</a>

<a id="880" class="Keyword">record</a> <a id="TestParams"></a><a id="887" href="Leios.Config.html#887" class="Record">TestParams</a> <a id="898" class="Symbol">(</a><a id="899" href="Leios.Config.html#899" class="Bound">params</a> <a id="906" class="Symbol">:</a> <a id="908" href="Leios.Config.html#778" class="Record">Params</a><a id="914" class="Symbol">)</a> <a id="916" class="Symbol">:</a> <a id="918" href="Agda.Primitive.html#388" class="Primitive">Type</a> <a id="923" class="Keyword">where</a>
  <a id="931" class="Keyword">open</a> <a id="936" href="Leios.Config.html#778" class="Module">Params</a> <a id="943" href="Leios.Config.html#899" class="Bound">params</a>

  <a id="953" class="Keyword">field</a> <a id="TestParams.sutId"></a><a id="959" href="Leios.Config.html#959" class="Field">sutId</a> <a id="965" class="Symbol">:</a> <a id="967" href="Data.Fin.Base.html#1132" class="Datatype">Fin</a> <a id="971" href="Leios.Config.html#625" class="Function">numberOfParties</a>
        <a id="TestParams.winning-slots"></a><a id="995" href="Leios.Config.html#995" class="Field">winning-slots</a> <a id="1009" class="Symbol">:</a> <a id="1011" href="abstract-set-theory.FiniteSetTheory.html#488" class="Function Operator">ℙ</a> <a id="1013" class="Symbol">(</a><a id="1014" href="Leios.Config.html#449" class="Datatype">BlockType</a> <a id="1024" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="1026" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="1027" class="Symbol">)</a>
</pre>
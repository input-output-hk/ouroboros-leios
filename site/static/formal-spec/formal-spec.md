This module serves as the main entry point for the Leios formal specification.
It imports all the core modules that together define the complete Leios protocol.
<!--
<pre class="Agda"><a id="175" class="Symbol">{-#</a> <a id="179" class="Keyword">OPTIONS</a> <a id="187" class="Pragma">--safe</a> <a id="194" class="Symbol">#-}</a>
</pre>-->
<pre class="Agda"><a id="214" class="Keyword">module</a> <a id="221" href="formal-spec.html" class="Module">formal-spec</a> <a id="233" class="Keyword">where</a>
</pre>The specification is organized into several key areas

### Prelude
TODO: move into iog-agda-prelude
<pre class="Agda"><a id="351" class="Keyword">open</a> <a id="356" class="Keyword">import</a> <a id="363" href="Prelude.Result.html" class="Module">Prelude.Result</a>
<a id="378" class="Keyword">open</a> <a id="383" class="Keyword">import</a> <a id="390" href="Prelude.Errors.html" class="Module">Prelude.Errors</a>
</pre>### Core Protocol Components
Abstract interface, specifing core types and functions
<pre class="Agda"><a id="501" class="Keyword">open</a> <a id="506" class="Keyword">import</a> <a id="513" href="Leios.Abstract.html" class="Module">Leios.Abstract</a>
</pre>Fundamental types and structures
<pre class="Agda"><a id="573" class="Keyword">open</a> <a id="578" class="Keyword">import</a> <a id="585" href="Leios.Base.html" class="Module">Leios.Base</a>
</pre>Block structure and validation
<pre class="Agda"><a id="639" class="Keyword">open</a> <a id="644" class="Keyword">import</a> <a id="651" href="Leios.Blocks.html" class="Module">Leios.Blocks</a>
</pre>Protocol parameters and configuration
<pre class="Agda"><a id="714" class="Keyword">open</a> <a id="719" class="Keyword">import</a> <a id="726" href="Leios.Config.html" class="Module">Leios.Config</a>
</pre>Freshest first delivery abstraction
<pre class="Agda"><a id="787" class="Keyword">open</a> <a id="792" class="Keyword">import</a> <a id="799" href="Leios.FFD.html" class="Module">Leios.FFD</a>
</pre>Key registration abstraction
<pre class="Agda"><a id="850" class="Keyword">open</a> <a id="855" class="Keyword">import</a> <a id="862" href="Leios.KeyRegistration.html" class="Module">Leios.KeyRegistration</a>
</pre>Project specific prelude
<pre class="Agda"><a id="921" class="Keyword">open</a> <a id="926" class="Keyword">import</a> <a id="933" href="Leios.Prelude.html" class="Module">Leios.Prelude</a>
</pre>Main protocol definition
<pre class="Agda"><a id="984" class="Keyword">open</a> <a id="989" class="Keyword">import</a> <a id="996" href="Leios.Protocol.html" class="Module">Leios.Protocol</a>
</pre>Abstractions bundled
<pre class="Agda"><a id="1044" class="Keyword">open</a> <a id="1049" class="Keyword">import</a> <a id="1056" href="Leios.SpecStructure.html" class="Module">Leios.SpecStructure</a>
</pre>Voting mechanism specification
<pre class="Agda"><a id="1119" class="Keyword">open</a> <a id="1124" class="Keyword">import</a> <a id="1131" href="Leios.Voting.html" class="Module">Leios.Voting</a>
</pre>Verifiable Random Function implementation
<pre class="Agda"><a id="1198" class="Keyword">open</a> <a id="1203" class="Keyword">import</a> <a id="1210" href="Leios.VRF.html" class="Module">Leios.VRF</a>
</pre>Linear Leios specification
<pre class="Agda"><a id="1259" class="Keyword">open</a> <a id="1264" class="Keyword">import</a> <a id="1271" href="Leios.Linear.html" class="Module">Leios.Linear</a>
</pre>### Cryptographic Foundations
Category-theoretic approach to cryptography
<pre class="Agda"><a id="1370" class="Keyword">open</a> <a id="1375" class="Keyword">import</a> <a id="1382" href="CategoricalCrypto.html" class="Module">CategoricalCrypto</a>
</pre>### Network Layer
Basic broadcast networking primitives
<pre class="Agda"><a id="1468" class="Keyword">open</a> <a id="1473" class="Keyword">import</a> <a id="1480" href="Network.BasicBroadcast.html" class="Module">Network.BasicBroadcast</a>
</pre>### Verification and Testing
Trace verification for protocol properties
<pre class="Agda"><a id="1587" class="Keyword">open</a> <a id="1592" class="Keyword">import</a> <a id="1599" href="Leios.Linear.Trace.Verifier.html" class="Module">Leios.Linear.Trace.Verifier</a>
<a id="1627" class="Keyword">open</a> <a id="1632" class="Keyword">import</a> <a id="1639" href="Leios.Linear.Trace.Verifier.Test.html" class="Module">Leios.Linear.Trace.Verifier.Test</a>
<a id="1672" class="Keyword">open</a> <a id="1677" class="Keyword">import</a> <a id="1684" href="Test.Defaults.html" class="Module">Test.Defaults</a>
</pre>
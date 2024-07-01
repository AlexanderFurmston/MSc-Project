file://<WORKSPACE>/testing/harnesses-code/sequoia-chinensis/src/main/scala/sequoiaChinensis.scala
### file%3A%2F%2F%2Fhome%2Fpigeon%2FDownloads%2Fmsc%2FMSc-Project%2Ftesting%2Fharnesses-code%2Fsequoia-chinensis%2Fsrc%2Fmain%2Fscala%2FsequoiaChinensis.scala:55: error: `:` expected but `)` found
  def entry(entryName: String, success: Boolean, time: String, hash: String, errmsg: String, contextCount): String = {
                                                                                                         ^

occurred in the presentation compiler.

presentation compiler configuration:
Scala version: 2.13.12
Classpath:
<HOME>/.cache/coursier/v1/https/repo1.maven.org/maven2/org/scala-lang/scala-library/2.13.12/scala-library-2.13.12.jar [exists ]
Options:



action parameters:
uri: file://<WORKSPACE>/testing/harnesses-code/sequoia-chinensis/src/main/scala/sequoiaChinensis.scala
text:
```scala
// This system must report everything that happens in a predefined format.

import scala.collection.JavaConverters._
import org.semanticweb.owlapi.model.OWLAxiom
import org.semanticweb.owlapi.model.OWLOntology
import com.sequoiareasoner.owlapi.SequoiaReasoner
import org.semanticweb.owlapi.model.IRI
import org.semanticweb.owlapi.util.InferredSubClassAxiomGenerator
import org.semanticweb.owlapi.util.InferredEquivalentClassAxiomGenerator
import org.semanticweb.owlapi.util.InferredAxiomGenerator
import org.semanticweb.owlapi.util.InferredOntologyGenerator
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat
import org.semanticweb.reasoner.Toolkit

object sequoiaChinensis {

  // Result list //
  var results: List[String] = List() 
  
  // Input Parameters //
  var inputFileName : String = ""
  var outputFolder: String = ""
  var debug: Boolean = false 
  var loadOnly: Boolean = false
  var consistency: Boolean = false 
  var printTime: Boolean = false
  var writeClassification: Boolean = false
  var hashClassification: Boolean = false
  
  // Print Input Parameters //
  def printParameters(): Unit = {
    System.out.println("TESTING PARAMETERS: ")
    System.out.println("   ** Input file: " + inputFileName)
    System.out.println("   ** Output folder: " + outputFolder)
    System.out.println("   ** Load Only Test?: " + yesno(loadOnly))
    System.out.println("   ** Consistency check only?: " + yesno(consistency))
    System.out.println("   ** Time Taxonomy?: " + yesno(printTime))
    System.out.println("   ** Write Taxonomy?: " + yesno(writeClassification))
    System.out.println("   ** Hash Taxonomy?: " + yesno(hashClassification))
  }

  // Print Dataset //
  def printDataset(): Unit = {
    System.out.println("Main Ontology: " + mainOntology.getOrElse("<UNIDENTIFIED>"))
    System.out.println("Extra Ontologies: " + extraOntologies.mkString(","))
  }

  // Main Ontology File //
  var mainOntology: Option[java.io.File] = None 
  
  // Extra Ontology Files //
  var extraOntologies: List[java.io.File] = List() 

  // Get Test Result Entry 
  def entry(entryName: String, success: Boolean, time: String, hash: String, errmsg: String, contextCount): String = {
    "<test>" + entryName + "</test>" + "<success>" + success.toString + "</success>" + "<time>" + time + "</time>" + "<hash>" + hash + "</hash>" + "<errmsg>" + errmsg + "</errmsg>" + "<contextCount>" + contextCount.toString + "</contextCount>"
  }

  // Utilities
  val stdout = System.out
  val basicTest: String = "BASIC"
  def yesno(boolean: Boolean): String = { if (boolean) {return "yes"} else {return "no"} }
 


  /// MAIN METHOD ///

  def main(args: Array[String]): Unit = {

    // new java.io.FileWriter("horn-Ontologies.txt", true) { write(args(0) + ", "); close}
    
	// Activate debug mode //
    debug = args.exists( arg => arg.contains("debug") )
    
    // Silence System.out //
    if (!debug) {
      System.setOut(new java.io.PrintStream(new java.io.OutputStream() {
      @throws[java.io.IOException]
      override def write(b: Int): Unit = { }
      }))
    }

    // Locate input file // 
    inputFileName = args(0)
    outputFolder = args(1)
    val inputFile: Option[java.io.File] = try Some(new java.io.File(inputFileName)) catch { case _: Exception =>  None }
   
    // Process input //
    for (argument <- args) argument match {
      case "load" => loadOnly = true
      case "consistency" => consistency = true
      case "time" => printTime = true
      case "write" => writeClassification = true
      case "hash" => hashClassification = true
      case _ =>
    }
    if (debug) printParameters 

    // Locate dataset //
    mainOntology = {
      inputFile flatMap { x => {
        if (x.isDirectory) x.listFiles.find(y => y.getName.endsWith(".owl")) 
        else {
          if (x.getName.endsWith(".owl")) Some(x)
          else None
        }}}}
    extraOntologies = {
      try {
        inputFile.get.listFiles.toList.filter( x => !x.getName.endsWith(".owl"))
      } catch {
        case e: Exception => extraOntologies
      }
    }
    if (debug) printDataset

    // Test ontologies //
    mainOntology match {
      case Some(ontology: java.io.File) => {
        // Main Ontology  
        val (btSuccess: Boolean, btTime: String, btHash: String, btErrorMsg: String, btContextCount: Int) = testOntologies(ontology)
          results = results :+ entry(basicTest,btSuccess,btTime,btHash,btErrorMsg,btContextCount) 
          if (debug) System.out.println(entry(basicTest,btSuccess,btTime,btHash,btErrorMsg,btContextCount)) 
        // Extra Ontologies 
        for (dataset <- extraOntologies) {
          val (tSuccess: Boolean, tTime: String, tHash: String, tErrorMsg: String, tContextCount: Int) = testOntologies(ontology,dataset)
          results = results :+ entry(dataset.toString,tSuccess,tTime,tHash,tErrorMsg,tContextCount)
          if (debug) System.out.println(entry(dataset.toString,tSuccess,tTime,tHash,tErrorMsg,tContextCount))
        }
      }
      case None => results = results :+ entry(basicTest,false,"","","Input file " + inputFileName + " not found.")
    }
   
    // Print Output and Exit //
    System.setOut(stdout)
    for (line <- results) {
      System.out.println(line)
    }
    System.exit(0)
  }



  // Method for testing ontologies //
  def testOntologies(mainOntology: java.io.File, sideOntology: java.io.File = new java.io.File("<none>") ): (Boolean,String,String,String,Integer) = {

    if (debug) System.out.println("///// TESTING ONTOLOGIES " + mainOntology.getName + " AND " + sideOntology.getName + "//////")

    // Create Ontology Manager //
    if (debug) System.out.println("Creating ontology manager...")
    val ontologyManager = org.semanticweb.owlapi.apibinding.OWLManager.createOWLOntologyManager
    if (debug) System.out.println("Ontology manager created.")

    // Load Main Ontology to Reasoner //
    var mOntology: OWLOntology = null
    if (debug) System.out.println("Loading main ontology to manager...")
    try {
      mOntology = ontologyManager.loadOntologyFromOntologyDocument(mainOntology)
    } catch {
      case e: Throwable => {
        if (debug) e.printStackTrace
        return(false,"","","Main ontology could not be loaded to manager",0)
      }
    }
    if (debug) System.out.println("Main ontology loaded to manager")
    
    // Load Side Ontology to Manager //
    var sOntology: OWLOntology = ontologyManager.createOntology 
    if (debug) System.out.println("Loading side ontology to manager...")
    try {
      sOntology = ontologyManager.loadOntologyFromOntologyDocument(sideOntology)
       if (debug) System.out.println("Side ontology loaded to manager")
    } catch {
      case e: Throwable => {
        if (debug) System.out.println("WARNING: Side ontology could not be loaded to manager. Proceeding without side ontology")
      }
    }
    
    // Merge ontologies //
    if (debug) System.out.println("Merging ontologies...") 
    for (axiom <- sOntology.getAxioms().asScala ) {
        ontologyManager.addAxiom(mOntology,axiom)
    }
    if (debug) System.out.println("The ontologies have been merged")
                                    
    // Create reasoner //
    var reasoner : SequoiaReasoner = null
    
    // Load ontology to reasoner // 
    if (debug) System.out.println("Loading ontology to reasoner...") 
    //var isHorn: Boolean = false  // DELETE 
    try {    
      reasoner = com.sequoiareasoner.owlapi.SequoiaReasonerFactory.getInstance.createReasoner(mOntology)
      //if (reasoner.getInternalReasoner.horn) isHorn = true // DELETE
    } catch {
      case e: Throwable => {
        if (debug) e.printStackTrace
        return (false,"","","Ontology could not be loaded to reasoner",0)
      }
    }
    if (debug) System.out.println("Ontology loaded to reasoner.")
    if (loadOnly) {
      if (debug) System.out.println("Load only test. Exiting...")
      //return (true,"","",yesno(isHorn)) // DELETE horn, write ""
    }

   // Reason, time, and hash // 
    val startTime = System.currentTimeMillis
    val testType: String = if (consistency) "consistency" else "classification"
    var time: String = "" 
    var hash: String = ""
    var havoc: Boolean = false 
    var contextCount: Int = 0
     
    if (debug) System.out.println("Starting " + testType + " test with reasoner...")
    try {
      if (consistency) {
        if (reasoner.isConsistent()) {hash = "CONSISTENT"} else {hash = "INCONSISTENT"}
	// havoc = reasoner.havocTriggered
        if (printTime) time = ((System.currentTimeMillis - startTime).toInt).toString
        if (debug) System.out.println("Consistency checked.")
        contextCount = reasoner.getInternalReasoner.getmanager.getAllContexts.size
        reasoner.dispose
        if (!havoc) return (true,time,hash,"",reasoner.getInternalReasoner.getmanager.getAllContexts.size) else return (false,time,"","NOMINALHAVOC",0)
      }
      else {
        reasoner.precomputeInferences(org.semanticweb.owlapi.reasoner.InferenceType.CLASS_HIERARCHY)
	// havoc = reasoner.havocTriggered
	if (debug) System.out.println("Ontology classified")
        if (printTime) time = ((System.currentTimeMillis - startTime).toInt).toString
        System.out.println("Contexts created (SeqChin) " + reasoner.getInternalReasoner.getmanager.getAllContexts.size)
        contextCount = reasoner.getInternalReasoner.getmanager.getAllContexts.size
        if (hashClassification) {
          import java.util
          var gens = new util.ArrayList[InferredAxiomGenerator[_ <: OWLAxiom]]
          gens.add(new InferredSubClassAxiomGenerator)
          gens.add(new InferredEquivalentClassAxiomGenerator)
          var classification = ontologyManager.createOntology
          val generator = new InferredOntologyGenerator(reasoner, gens)
          generator.fillOntology(ontologyManager.getOWLDataFactory, classification)
          if (debug) System.out.println("Hashing...")
          hash = Toolkit.getHash(classification).toString
          if (debug) System.out.println("Hash complete.")
          if (writeClassification) {
            if (debug) System.out.println("Writing taxonomy...")
            val outputFileName: String = inputFileName + "." + "CLASSIFIED.SEQUOIA.AFFINIS"
            try {
              ontologyManager.saveOntology(classification, new FunctionalSyntaxDocumentFormat, IRI.create((new java.io.File(outputFolder + "/" + outputFileName).toURI())))
              if (debug) System.out.println("Writing successful")
            } catch {
              case e : Exception => System.out.println("Cannot save " + outputFileName + "!")
            }
		  }
		}
        reasoner.dispose
        if (!havoc) return (true,time,hash,"",contextCount) else return (false,time,"","NOMINALHAVOC",contextCount)
      }
    } catch {
      case e: Throwable => {
        if (debug) e.printStackTrace
        reasoner.dispose
        return(false,"","","Reasoner produced an exception",0)
      }
    }
  }


}


```



#### Error stacktrace:

```
scala.meta.internal.parsers.Reporter.syntaxError(Reporter.scala:16)
	scala.meta.internal.parsers.Reporter.syntaxError$(Reporter.scala:16)
	scala.meta.internal.parsers.Reporter$$anon$1.syntaxError(Reporter.scala:22)
	scala.meta.internal.parsers.Reporter.syntaxError(Reporter.scala:17)
	scala.meta.internal.parsers.Reporter.syntaxError$(Reporter.scala:17)
	scala.meta.internal.parsers.Reporter$$anon$1.syntaxError(Reporter.scala:22)
	scala.meta.internal.parsers.ScalametaParser.scala$meta$internal$parsers$ScalametaParser$$expectAt(ScalametaParser.scala:389)
	scala.meta.internal.parsers.ScalametaParser.scala$meta$internal$parsers$ScalametaParser$$expectAt(ScalametaParser.scala:393)
	scala.meta.internal.parsers.ScalametaParser.expect(ScalametaParser.scala:395)
	scala.meta.internal.parsers.ScalametaParser.accept(ScalametaParser.scala:411)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$termParam$11(ScalametaParser.scala:3069)
	scala.Option.getOrElse(Option.scala:201)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$termParam$1(ScalametaParser.scala:3060)
	scala.meta.internal.parsers.ScalametaParser.atPos(ScalametaParser.scala:319)
	scala.meta.internal.parsers.ScalametaParser.autoPos(ScalametaParser.scala:363)
	scala.meta.internal.parsers.ScalametaParser.termParam(ScalametaParser.scala:3007)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$termParamClausesOnParen$4(ScalametaParser.scala:2965)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$termParamClausesOnParen$4$adapted(ScalametaParser.scala:2965)
	scala.meta.internal.parsers.ScalametaParser.iter$1(ScalametaParser.scala:622)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$tokenSeparated$1(ScalametaParser.scala:627)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$tokenSeparated$1$adapted(ScalametaParser.scala:615)
	scala.meta.internal.parsers.ScalametaParser.scala$meta$internal$parsers$ScalametaParser$$listBy(ScalametaParser.scala:555)
	scala.meta.internal.parsers.ScalametaParser.tokenSeparated(ScalametaParser.scala:615)
	scala.meta.internal.parsers.ScalametaParser.commaSeparatedWithIndex(ScalametaParser.scala:636)
	scala.meta.internal.parsers.ScalametaParser.parseParams$1(ScalametaParser.scala:2965)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$termParamClausesOnParen$2(ScalametaParser.scala:2975)
	scala.meta.internal.parsers.ScalametaParser.scala$meta$internal$parsers$ScalametaParser$$inParensAfterOpenOr(ScalametaParser.scala:247)
	scala.meta.internal.parsers.ScalametaParser.scala$meta$internal$parsers$ScalametaParser$$inParensOnOpenOr(ScalametaParser.scala:238)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$termParamClausesOnParen$1(ScalametaParser.scala:2977)
	scala.meta.internal.parsers.ScalametaParser.atPos(ScalametaParser.scala:319)
	scala.meta.internal.parsers.ScalametaParser.autoPos(ScalametaParser.scala:363)
	scala.meta.internal.parsers.ScalametaParser.paramClause$1(ScalametaParser.scala:2977)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$termParamClausesOnParen$8(ScalametaParser.scala:2981)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$termParamClausesOnParen$8$adapted(ScalametaParser.scala:2980)
	scala.meta.internal.parsers.ScalametaParser.scala$meta$internal$parsers$ScalametaParser$$listBy(ScalametaParser.scala:555)
	scala.meta.internal.parsers.ScalametaParser.termParamClausesOnParen(ScalametaParser.scala:2980)
	scala.meta.internal.parsers.ScalametaParser.termParamClauses(ScalametaParser.scala:2949)
	scala.meta.internal.parsers.ScalametaParser.nonInterleavedParamClauses$1(ScalametaParser.scala:3510)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$funDefRest$1(ScalametaParser.scala:3516)
	scala.meta.internal.parsers.ScalametaParser.autoEndPos(ScalametaParser.scala:366)
	scala.meta.internal.parsers.ScalametaParser.autoEndPos(ScalametaParser.scala:371)
	scala.meta.internal.parsers.ScalametaParser.funDefRest(ScalametaParser.scala:3495)
	scala.meta.internal.parsers.ScalametaParser.funDefOrDclOrExtensionOrSecondaryCtor(ScalametaParser.scala:3444)
	scala.meta.internal.parsers.ScalametaParser.defOrDclOrSecondaryCtor(ScalametaParser.scala:3304)
	scala.meta.internal.parsers.ScalametaParser.nonLocalDefOrDcl(ScalametaParser.scala:3283)
	scala.meta.internal.parsers.ScalametaParser$$anonfun$templateStat$1.applyOrElse(ScalametaParser.scala:4137)
	scala.meta.internal.parsers.ScalametaParser$$anonfun$templateStat$1.applyOrElse(ScalametaParser.scala:4134)
	scala.PartialFunction.$anonfun$runWith$1(PartialFunction.scala:231)
	scala.PartialFunction.$anonfun$runWith$1$adapted(PartialFunction.scala:230)
	scala.meta.internal.parsers.ScalametaParser.statSeqBuf(ScalametaParser.scala:4094)
	scala.meta.internal.parsers.ScalametaParser.getStats$2(ScalametaParser.scala:4124)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$scala$meta$internal$parsers$ScalametaParser$$templateStatSeq$3(ScalametaParser.scala:4125)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$scala$meta$internal$parsers$ScalametaParser$$templateStatSeq$3$adapted(ScalametaParser.scala:4123)
	scala.meta.internal.parsers.ScalametaParser.scala$meta$internal$parsers$ScalametaParser$$listBy(ScalametaParser.scala:555)
	scala.meta.internal.parsers.ScalametaParser.scala$meta$internal$parsers$ScalametaParser$$templateStatSeq(ScalametaParser.scala:4123)
	scala.meta.internal.parsers.ScalametaParser.scala$meta$internal$parsers$ScalametaParser$$templateStatSeq(ScalametaParser.scala:4115)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$templateBody$1(ScalametaParser.scala:3993)
	scala.meta.internal.parsers.ScalametaParser.inBracesOr(ScalametaParser.scala:254)
	scala.meta.internal.parsers.ScalametaParser.inBraces(ScalametaParser.scala:250)
	scala.meta.internal.parsers.ScalametaParser.templateBody(ScalametaParser.scala:3993)
	scala.meta.internal.parsers.ScalametaParser.templateBodyOpt(ScalametaParser.scala:3996)
	scala.meta.internal.parsers.ScalametaParser.templateAfterExtends(ScalametaParser.scala:3947)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$templateOpt$1(ScalametaParser.scala:3988)
	scala.meta.internal.parsers.ScalametaParser.atPos(ScalametaParser.scala:319)
	scala.meta.internal.parsers.ScalametaParser.autoPos(ScalametaParser.scala:363)
	scala.meta.internal.parsers.ScalametaParser.templateOpt(ScalametaParser.scala:3980)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$objectDef$1(ScalametaParser.scala:3706)
	scala.meta.internal.parsers.ScalametaParser.autoEndPos(ScalametaParser.scala:366)
	scala.meta.internal.parsers.ScalametaParser.autoEndPos(ScalametaParser.scala:371)
	scala.meta.internal.parsers.ScalametaParser.objectDef(ScalametaParser.scala:3698)
	scala.meta.internal.parsers.ScalametaParser.tmplDef(ScalametaParser.scala:3585)
	scala.meta.internal.parsers.ScalametaParser.topLevelTmplDef(ScalametaParser.scala:3573)
	scala.meta.internal.parsers.ScalametaParser$$anonfun$2.applyOrElse(ScalametaParser.scala:4108)
	scala.meta.internal.parsers.ScalametaParser$$anonfun$2.applyOrElse(ScalametaParser.scala:4102)
	scala.PartialFunction.$anonfun$runWith$1(PartialFunction.scala:231)
	scala.PartialFunction.$anonfun$runWith$1$adapted(PartialFunction.scala:230)
	scala.meta.internal.parsers.ScalametaParser.statSeqBuf(ScalametaParser.scala:4094)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$batchSource$13(ScalametaParser.scala:4304)
	scala.Option.getOrElse(Option.scala:201)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$batchSource$1(ScalametaParser.scala:4304)
	scala.meta.internal.parsers.ScalametaParser.atPos(ScalametaParser.scala:319)
	scala.meta.internal.parsers.ScalametaParser.autoPos(ScalametaParser.scala:363)
	scala.meta.internal.parsers.ScalametaParser.batchSource(ScalametaParser.scala:4261)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$source$1(ScalametaParser.scala:4255)
	scala.meta.internal.parsers.ScalametaParser.atPos(ScalametaParser.scala:319)
	scala.meta.internal.parsers.ScalametaParser.autoPos(ScalametaParser.scala:363)
	scala.meta.internal.parsers.ScalametaParser.source(ScalametaParser.scala:4255)
	scala.meta.internal.parsers.ScalametaParser.entrypointSource(ScalametaParser.scala:4259)
	scala.meta.internal.parsers.ScalametaParser.parseSourceImpl(ScalametaParser.scala:119)
	scala.meta.internal.parsers.ScalametaParser.$anonfun$parseSource$1(ScalametaParser.scala:116)
	scala.meta.internal.parsers.ScalametaParser.parseRuleAfterBOF(ScalametaParser.scala:58)
	scala.meta.internal.parsers.ScalametaParser.parseRule(ScalametaParser.scala:53)
	scala.meta.internal.parsers.ScalametaParser.parseSource(ScalametaParser.scala:116)
	scala.meta.parsers.Parse$.$anonfun$parseSource$1(Parse.scala:30)
	scala.meta.parsers.Parse$$anon$1.apply(Parse.scala:37)
	scala.meta.parsers.Api$XtensionParseDialectInput.parse(Api.scala:22)
	scala.meta.internal.semanticdb.scalac.ParseOps$XtensionCompilationUnitSource.toSource(ParseOps.scala:15)
	scala.meta.internal.semanticdb.scalac.TextDocumentOps$XtensionCompilationUnitDocument.toTextDocument(TextDocumentOps.scala:179)
	scala.meta.internal.pc.SemanticdbTextDocumentProvider.textDocument(SemanticdbTextDocumentProvider.scala:54)
	scala.meta.internal.pc.ScalaPresentationCompiler.$anonfun$semanticdbTextDocument$1(ScalaPresentationCompiler.scala:462)
```
#### Short summary: 

file%3A%2F%2F%2Fhome%2Fpigeon%2FDownloads%2Fmsc%2FMSc-Project%2Ftesting%2Fharnesses-code%2Fsequoia-chinensis%2Fsrc%2Fmain%2Fscala%2FsequoiaChinensis.scala:55: error: `:` expected but `)` found
  def entry(entryName: String, success: Boolean, time: String, hash: String, errmsg: String, contextCount): String = {
                                                                                                         ^
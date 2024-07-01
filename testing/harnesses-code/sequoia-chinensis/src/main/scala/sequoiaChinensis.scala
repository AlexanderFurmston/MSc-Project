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
  def entry(entryName: String, success: Boolean, time: String, hash: String, errmsg: String, contextCount: Int): String = {
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
      case None => results = results :+ entry(basicTest,false,"","","Input file " + inputFileName + " not found.", 0)
    }
   
    // Print Output and Exit //
    System.setOut(stdout)
    for (line <- results) {
      System.out.println(line)
    }
    System.exit(0)
  }



  // Method for testing ontologies //
  def testOntologies(mainOntology: java.io.File, sideOntology: java.io.File = new java.io.File("<none>") ): (Boolean,String,String,String,Int) = {

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


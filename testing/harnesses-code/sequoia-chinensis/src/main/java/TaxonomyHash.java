package org.semanticweb.reasoner;

import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.util.OWLObjectVisitorAdapter;

public class TaxonomyHash extends OWLObjectVisitorAdapter {

	private int iriHash = 0;

	private int classHash = 0;

	private int axiomHash = 0;

	private int ontologyHash = 0;

	private final static TaxonomyHash INSTANCE = new TaxonomyHash();

	@Override
	protected void handleDefault(OWLObject object) {
		throw new RuntimeException(
				"Unexpected expression in taxonomy: " + object);
	}

	@Override
	public void visit(OWLSubClassOfAxiom axiom) {
		axiomHash = 0;
		axiom.getSubClass().accept(this);
		axiomHash += 3 * classHash;
		axiom.getSuperClass().accept(this);
		axiomHash += 5 * classHash;
	}

	@Override
	public void visit(OWLEquivalentClassesAxiom axiom) {
		axiomHash = 0;
		for (OWLClassExpression ce : axiom.getClassExpressions()) {
			ce.accept(this);
			axiomHash += 7 * classHash;
		}
	}

	@Override
	public void visit(OWLClass ce) {
		ce.getIRI().accept(this);
		classHash = 11 * iriHash;
	}

	@Override
	public void visit(IRI iri) {
		iriHash = iri.hashCode();
	}

	@Override
	public void visit(OWLOntology ontology) {
		ontologyHash = 0;
		for (OWLAxiom axiom : ontology.getAxioms()) {
			axiom.accept(this);
			ontologyHash += 13 * axiomHash;
		}
	}

	public static int hashCode(OWLAxiom axiom) {
		axiom.accept(INSTANCE);
		return INSTANCE.axiomHash;
	}

	public static int hashCode(OWLOntology ontology) {
		ontology.accept(INSTANCE);
		return INSTANCE.ontologyHash;
	}

}

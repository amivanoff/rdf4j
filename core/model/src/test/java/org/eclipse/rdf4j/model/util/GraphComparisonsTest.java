package org.eclipse.rdf4j.model.util;

import static org.eclipse.rdf4j.model.util.Values.bnode;
import static org.eclipse.rdf4j.model.util.Values.iri;

import java.util.Map;

import org.eclipse.rdf4j.model.BNode;
import org.eclipse.rdf4j.model.IRI;
import org.eclipse.rdf4j.model.Model;
import org.eclipse.rdf4j.model.Value;
import org.eclipse.rdf4j.model.impl.LinkedHashModel;
import org.eclipse.rdf4j.model.impl.TreeModel;
import org.eclipse.rdf4j.model.vocabulary.RDF;
import org.junit.Test;

public class GraphComparisonsTest {

	private static final String ex = "http://example.org/";

	@Test
	public void testHashing() {

		Model model1 = new TreeModel();
		Model model2 = new LinkedHashModel();

		BNode node1 = bnode();
		IRI foo = iri(ex, "foo");
		IRI bar = iri(ex, "bar");
		model1.add(foo, RDF.TYPE, node1);
		model1.add(node1, RDF.TYPE, bar);

		BNode node2 = bnode();
		model2.add(foo, RDF.TYPE, node2);
		model2.add(node2, RDF.TYPE, foo);

		Map<Value, Integer> result1 = GraphComparisons.createCanonicalHashes(model1);

		Map<Value, Integer> result2 = GraphComparisons.createCanonicalHashes(model2);
		result1.entrySet().forEach(System.out::println);
		result2.entrySet().forEach(System.out::println);
	}
}

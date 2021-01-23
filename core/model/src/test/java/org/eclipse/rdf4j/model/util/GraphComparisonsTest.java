package org.eclipse.rdf4j.model.util;

import static org.assertj.core.api.Assertions.assertThat;
import static org.eclipse.rdf4j.model.util.Values.bnode;
import static org.eclipse.rdf4j.model.util.Values.iri;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Map;

import org.eclipse.rdf4j.model.BNode;
import org.eclipse.rdf4j.model.IRI;
import org.eclipse.rdf4j.model.Model;
import org.eclipse.rdf4j.model.Value;
import org.eclipse.rdf4j.model.impl.LinkedHashModel;
import org.eclipse.rdf4j.model.impl.TreeModel;
import org.eclipse.rdf4j.model.vocabulary.RDF;
import org.junit.Test;

import com.google.common.hash.HashCode;

public class GraphComparisonsTest {

	private static final String ex = "http://example.org/";

	IRI p = iri(ex, "p"), q = iri(ex, "q");
	BNode a = bnode("a"), b = bnode("b"), c = bnode("c"), d = bnode("d"), e = bnode("e"), f = bnode("f"),
			g = bnode("g"), h = bnode("h"), i = bnode("i");

	@Test
	public void testCanonicalHashing() {
		Model example49 = buildExample49Model();

		Map<BNode, HashCode> mapping = GraphComparisons.hashBNodes(example49);

		assertThat(mapping.get(a))
				.isEqualTo(mapping.get(c))
				.isEqualTo(mapping.get(g))
				.isEqualTo(mapping.get(i));

		assertThat(mapping.get(b))
				.isEqualTo(mapping.get(d))
				.isEqualTo(mapping.get(f))
				.isEqualTo(mapping.get(h));

		assertThat(mapping.get(a)).isNotEqualTo(mapping.get(b));
		assertThat(mapping.get(e)).isNotEqualTo(mapping.get(a))
				.isNotEqualTo(mapping.get(b));
	}

	@Test
	public void testPartition() {
		Model example49 = buildExample49Model();

		Collection<Collection<BNode>> partition = GraphComparisons
				.partition(GraphComparisons.hashBNodes(example49));

		assertThat(partition).hasSize(3);
	}

	@Test
	public void testIsoCanonicalize() {
		Model example49 = buildExample49Model();

		Model canonicalized = GraphComparisons.isoCanonicalize(example49);

		assertThat(canonicalized.size()).isEqualTo(example49.size());

		canonicalized.forEach(System.out::println);
	}

	@Test
	public void testIsomorphic() {
		Model example49 = buildExample49Model();
		Model isomorphic = buildExample49ModelIsomorphic();

		assertThat(GraphComparisons.isomorphic(example49, isomorphic));
	}

	@Test
	public void testShaclReportsIsomorphic() {

	}

	private Model buildExample49Model() {
		// @formatter:off
		Model example49 = new ModelBuilder(new LinkedHashModel())
				.subject(a).add(p, b).add(p, d)
				.subject(b).add(q, e)
				.subject(c).add(p, b).add(p, f)
				.subject(d).add(q, e)
				.subject(f).add(q, e)
				.subject(g).add(p, d).add(p, h)
				.subject(h).add(q, e)
				.subject(i).add(p, f).add(p, h)
				.build();
		// @formatter:on

		return example49;
	}

	private Model buildExample49ModelIsomorphic() {
		// @formatter:off
		Model example49 = new ModelBuilder(new LinkedHashModel())
				.subject(bnode("other-i")).add(p, bnode("other-f")).add(p, bnode("other-h"))
				.subject(bnode("other-a")).add(p, bnode("other-b")).add(p, bnode("other-d"))
				.subject(bnode("other-b")).add(q, bnode("other-e"))
				.subject(bnode("other-c")).add(p, bnode("other-b")).add(p, bnode("other-f"))
				.subject(bnode("other-f")).add(q, bnode("other-e"))
				.subject(bnode("other-d")).add(q, bnode("other-e"))
				.subject(bnode("other-g")).add(p, bnode("other-d")).add(p, bnode("other-h"))
				.subject(bnode("other-h")).add(q, bnode("other-e"))
				.build();
		// @formatter:on

		return example49;
	}
}

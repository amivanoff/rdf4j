package org.eclipse.rdf4j.sail.shacl.planNodes;

import org.apache.commons.lang.StringEscapeUtils;
import org.eclipse.rdf4j.common.iteration.CloseableIteration;
import org.eclipse.rdf4j.sail.SailException;

import java.util.ArrayDeque;
import java.util.Queue;

public class BufferedPlanNode<T extends MultiStreamPlanNode & PlanNode> implements PushablePlanNode {

	private T parent;

	private Queue<Tuple> buffer = new ArrayDeque<>();
	private boolean closed;
	private boolean printed;


	BufferedPlanNode(T parent) {
		this.parent = parent;
	}

	@Override
	public CloseableIteration<Tuple, SailException> iterator() {
		return new CloseableIteration<Tuple, SailException>() {

			{
				parent.init();
			}

			@Override
			public void close() throws SailException {
				closed = true;
				parent.close();
			}

			@Override
			public boolean hasNext() throws SailException {
				calculateNext();
				return !buffer.isEmpty();
			}

			private void calculateNext() {
				while (buffer.isEmpty()) {
					boolean success = parent.incrementIterator();
					if (!success) {
						break;
					}
				}
			}

			@Override
			public Tuple next() throws SailException {
				calculateNext();
				return buffer.remove();
			}

			@Override
			public void remove() throws SailException {

			}
		};
	}

	@Override
	public int depth() {
		return parent.depth();
	}

	@Override
	public void getPlanAsGraphvizDot(StringBuilder stringBuilder) {
		if (printed) {
			return;
		}
		printed = true;
		parent.getPlanAsGraphvizDot(stringBuilder);

		stringBuilder.append(getId() + " [label=\"" + StringEscapeUtils.escapeJava(this.toString()) + "\"];").append("\n");
	}

	@Override
	public String getId() {
		return System.identityHashCode(this) + "";
	}

	@Override
	public IteratorData getIteratorDataType() {
		return parent.getIteratorDataType();
	}

	@Override
	public void push(Tuple next) {
		buffer.add(next);
	}

	@Override
	public boolean isClosed() {
		return closed;
	}

	@Override
	public String toString() {
		return "BufferedPlanNode";
	}
}

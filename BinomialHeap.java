import java.util.HashSet;

/**
 * BinomialHeap
 * An implementation of binomial heap over non-negative integers.
 * Based on exercise from previous semester.
 */
public class BinomialHeap
{
	public int size;
	public HeapNode last;
	public HeapNode min;
	protected int numTrees; // maintained as a field for efficiency


	// default constructor
	public BinomialHeap() {
		last = null;
		min = null;
		size = 0;
		numTrees = 0;
	}

	/**
	 * initializing heap from a list of binomial trees,
	 * node is the last node in the list.
	 * used on children of deleted node for melding
	 **/
	public BinomialHeap(HeapNode node) {
		last = node;
		size = 0;
		min = node;
		numTrees = 0;
		do {
			numTrees++;
			if (node.getKey() < min.getKey()) {
				min = node;
			}
			size += Math.pow(2, node.getRank());
			node.parent = null;
			node = node.getNext();
		}
		while (node != last);
	}

	/**
	 *
	 * pre: key > 0
	 * Insert (key,info) into the heap and return the newly generated HeapItem.
	 *
	 */
	public HeapItem insert(int key, String info) {
		HeapItem item = new HeapItem(key, info);
		HeapNode node = item.getNode();

		increaseSize(1);
		updateTreeNum(true);

		if (size()==1){ // first node in heap
			setMin(node);
			setLast(node);
		}
		else {
			if (minKey() > key) { // update min if needed
				setMin(node);
			}
			getLast().addNext(node); // add node to the beginning of the heap
			if (size() % 2 == 0) { // if there's another rank-1 tree, start the linking process
				this.unify(node);
			}
		}
		return item;
	}

	/**
	 * Delete the minimal item
	 */
	public void deleteMin()
	{
		HeapNode curMin = getMin();

		if (curMin.getNext() == curMin) { // only one node in heap
			setMin(null);
			setLast(null);
		}
		else {
			HeapNode prev = setNewMin(curMin);
			// prev is the node before curMin
			if (getLast() == curMin) {  // update last if needed
				setLast(prev);
			}
		}

		HeapNode minChildren = curMin.getChild();
		curMin.setChild(null);
		detach(curMin); // remove the minimum node from heap
		if (minChildren != null){ // if min has sons, create a new heap from them and meld with this heap
			BinomialHeap orphans = new BinomialHeap(minChildren);
			meld(orphans);
		}
	}

	/**
	 * Return the minimal HeapItem
	 */
	public HeapItem findMin()
	{

		if (empty()) return null;
		return this.min.item;
	}

	/**
	 * Return the number of elements in the heap
	 */
	public int size() {
		return this.size; // should be replaced by student code
	}

	/**
	 * The method returns true if and only if the heap
	 * is empty.
	 */
	public boolean empty() {
		return (this.size==0);
	}

	/**
	 * Return the number of trees in the heap.
	 */
	public int numTrees() {
		return this.numTrees;
	}

	/**
	 * pre: 0 < diff < item.key
	 * Decrease the key of item by diff and fix the heap.
	 */
	public void decreaseKey(HeapItem item, int diff)
	{
		item.decKey(diff);
		siftUp(item.getNode()); // sift up the node until heap is fixed
		if (item.getKey() < minKey()){ // update min if needed
			setMin(item.getNode());
		}
	}

	/**
	 * Delete the item from the heap.
	 */
	public void delete(HeapItem item)
	{
		this.decreaseKey(item, item.getKey()+1);
		this.deleteMin();
	}

	/**
	 * Meld the heap with heap2
	 */
	public void meld(BinomialHeap heap2)
	{
		if (heap2.empty()) return;
		if (this.empty()){
			assign(heap2);
		}
		else {
			// no need to use merge & unify if one of the heaps is empty
			HeapNode pointer = this.merge(heap2);
			unify(pointer);
		}
		heap2.reset();
	}

	/**
	 * pre: curMin is the current minimal node in heap
	 * updates heap's min to the node with the next minimal key after curMin
	 * returns the node before curMin
	 */
	protected HeapNode setNewMin(HeapNode curMin){
		HeapNode next = curMin.getNext();
		setMin(next);
		int minK = next.getKey();
		while (next.getNext() != curMin){
			next = next.getNext();
			if (next.getKey() < minK){
				setMin(next);
				minK = next.getKey();
			}
		}
		return next;
	}


	/**
	 *  sift up
	 */
	public void siftUp(HeapNode node){
		HeapNode nodePar = node.getParent();
		HeapItem nodeItem;
		HeapItem parItem;

		while (nodePar!= null && node.getKey() <= nodePar.getKey()) {
			// swap node's and nodePar's items until heap is fixed
			nodeItem = node.getItem();
			parItem = nodePar.getItem();

			nodeItem.setNode(nodePar);
			nodePar.setItem(nodeItem);
			parItem.setNode(node);
			node.setItem(parItem);

			node = nodePar;
			nodePar = nodePar.getParent();
		}
	}

	/**
	 * detach
	 */
	private void detach(HeapNode node, boolean permanentRemove) {
		HeapNode next = node.getNext();
		HeapNode par = node.getParent();

		if (par != null){ // node is not a root
			if (par.getChild().equals(node)){ // node is the highest-rank child
				par.setRank((next==null) ? 0 : next.getRank()+1); // update parent's rank
				par.setChild(next);
			}
			node.setParent(null);
		}
		else if (permanentRemove){ // node is a root & this is a permanent removal
			updateTreeNum(false);
		}

		if (next != node) {  // node has siblings
			HeapNode pre = next; // find node's previous sibling
			while (pre.getNext() != node) {
				pre = pre.getNext();
			}
			pre.setNext(next); // remove node from siblings list
			node.setNext(node);
		}
		if (permanentRemove){ // update size if needed
			increaseSize( -(int)Math.pow(2, node.getRank()) );
		}
	}

	private void detach(HeapNode node){
		//default size updating, for permanent removals
		detach(node, true);
	}

	/**
	 * adds the roots of heap2 to the roots list of this heap,
	 * ordered by rank (ascending).
	 * after- this heap is temporary *not* a binomial heap!
	 * returns: the first root of the new heap
	 */
	private HeapNode merge(BinomialHeap heap2){
		increaseSize(heap2.size());
		addTreeNum(heap2.numTrees());

		if (minKey() > heap2.minKey()) { // update min if needed
			setMin(heap2.getMin());
		}

		HeapNode prev = getLast();
		HeapNode pointer1 = getLast().getNext();
		HeapNode pointer2 = heap2.getLast().getNext();
		HeapNode first = pointer1;

		// will iterate until all node's ranks in heap2 are higher than in this
		do {
			int compare = Integer.compare(pointer1.getRank(), pointer2.getRank());
			if (compare < 0){  // pointer1's rank is lower than pointer2's rank
				// pointer2 merges into heap only if its rank <= pointer1's rank, to keep legality
				prev = pointer1;
				pointer1 = pointer1.getNext();
			}
			else {
				HeapNode temp = pointer2.getNext();
				heap2.detach(pointer2); // detach pointer2 from heap2

				if (compare > 0 ){ // pointer1's rank is higher than pointer2's rank
					prev.addNext(pointer2);
					prev = pointer2;
				}
				else {  // pointer1's rank is equal to pointer2's rank
					pointer1.addNext(pointer2);
					prev = pointer1;
					pointer1 = pointer2;
				}
				pointer2 = temp;
			}
		}
		while (pointer1 != getLast().getNext() && heap2.size() > 0);

		int idx = 1;
		HeapNode last = first;
		while (last.getNext().getRank() >= last.getRank() && idx < numTrees()){
			// finds the current last node in the roots list
			last = last.getNext();
			idx++;
		}
		first = last.getNext(); // current first-root

		if (heap2.size() > 0) {   // adds the remaining of heap2 into heap1
			HeapNode last2 = heap2.getLast();
			last.setNext(last2.getNext());
			last = last2; // current last-root
			last.setNext(first);
		}
		setLast(last);
		return first;
	}

	/**
	 * pre: self is an almost-heap (linkedList of binomial trees roots)
	 * param: receives the first node in the roots list
	 * links the trees to form a legal binomial heap
	 * */
	private void unify(HeapNode pointer){
		HeapNode prev = this.getLast();
		HeapNode next= pointer.getNext();
		boolean setMin;
		boolean setLast;

		do {
			if (pointer.getRank() == next.getRank()){ // if ranks are equal, merge
				if (next.getNext() != pointer && pointer.getRank() == next.getNext().getRank()){
					// if there are 3 consecutive trees with the same rank, move on to merge the last 2
					prev = pointer;
					pointer = next;
					next = pointer.getNext();
				}

				setMin = (getMin() == next || getMin() == pointer);
				// if next.key=pointer.key=min.key, min-node may not be a root after linking
				setLast = (getLast() == next || getLast() == pointer);
				// if last.key < other.key, last-root will no longer be root after linking

				detach(pointer, false); // temporarily detach the trees from the heap
				detach(next, false);
				pointer = pointer.link(next);  // link the trees properly
				if (setMin){ setMin(pointer); }
				if (setLast){ setLast(pointer); }
				if (prev != next){ // unless this is the entire heap, add back to the roots list
					prev.addNext(pointer);
				}
				updateTreeNum(false);
			}
			else {  // move on to the next tree
				prev = pointer;
				pointer = next;
			}
			next = pointer.getNext();
		}
		while (pointer != this.getLast() && pointer != next);

	}

	/**
	 * changes this heap to be same on heap2
	 */
	private void assign(BinomialHeap heap2){
		setMin(heap2.getMin());
		setLast(heap2.getLast());
		setSize(heap2.size());
		setTreeNum(heap2.numTrees());
	}

	/**
	 * resets the heap to an empty heap
	 */
	private void reset(){
		setMin(null);
		setLast(null);
		setSize(0);
		setTreeNum(0);
	}


	/**
	 *
	 * getters & setters
	 *
	 */
	protected HeapNode getMin(){
		return this.min;
	}
	protected int minKey(){
		return this.min.item.key;
	}
	protected HeapNode getLast(){
		return this.last;
	}
	protected void setMin(HeapNode node){
		this.min = node;
	}
	protected void setLast(HeapNode node){
		this.last = node;
	}
	protected void setSize(int size){
		this.size = size;
	}
	protected void increaseSize(int num){
		this.size += num;
	}
	protected void updateTreeNum(boolean increase){
		if (increase) { numTrees++; }
		else { numTrees--; }
	}
	protected void addTreeNum(int num){
		numTrees += num;
	}
	protected void setTreeNum(int num) {
		this.numTrees= num;
	}


	@Override
	public String toString(){
		if(empty()){
			return "Binomial Heap is empty";
		}

		HashSet<HeapNode> visited = new HashSet<>();
		return "Heap fields: " + System.lineSeparator() +
				String.format("{size: %d, min: %d, last: %d, first: %d}",
						size(), minKey(), getLast().getKey(), getLast().getNext().getKey()) +
				String.format("%s%s----- Heap Nodes: -----%s",
						System.lineSeparator(),System.lineSeparator(),System.lineSeparator())
				+ nodesRep(getLast().getNext(), 0, visited);
	}

	protected String nodesRep(HeapNode node, int indentLevel, HashSet<HeapNode> visited){
		StringBuilder indent = new StringBuilder();
		indent.append("                ".repeat(Math.max(0, indentLevel)));
		StringBuilder rep = new StringBuilder();
		//rep.append(node.toString(indent.toString())).append(System.lineSeparator());             //full info
		rep.append(indent).append(node.getItem().toString()).append(System.lineSeparator());   //only basic info
		visited.add(node);

		if (node.getChild() != null && !visited.contains(node.getChild())) {
			rep.append(String.format("%s           ---->%s", indent, System.lineSeparator()));
			rep.append(nodesRep(node.getChild().getNext(), indentLevel + 1, visited));
		}
		if (node.getNext() != null && !visited.contains(node.getNext())) {
			rep.append(String.format("%s |%s", indent, System.lineSeparator()));
			rep.append(nodesRep(node.getNext(), indentLevel, visited));
		}
		return rep.toString();
	}


	/**
	 *
	 * Class implementing a node in a Binomial Heap.
	 *
	 */
	public class HeapNode{
		public HeapItem item;
		public HeapNode child;
		public HeapNode next;
		public HeapNode parent;
		public int rank;

		/**
		 * default constructor
		 * sets node with self-loop
		 */
		public HeapNode(){
			this.next = this;
			this.rank = 0;
		}

		/**
		 * connects new HeapNode next to this
		 **/
		protected void addNext(HeapNode node){
			HeapNode par = getParent();
			if (par!=null && node.getRank()>par.getChild().getRank()){
				// if node's rank is higher than current-child's, make node the new child
				par.setChild(node);
				par.setRank(node.getRank()+1); // update parent's rank accordingly
			}
			node.setParent(par);
			node.setNext(getNext());
			setNext(node);
		}

		/**
		 * connects the HeapNode's subtree to binomial tree of same degree
		 * param: the root of the linked binomial tree
		 * return: the root of the new heap (smaller-key node)
		 **/
		private HeapNode link(HeapNode root) {
			HeapNode son = this;
			if (getKey() < root.getKey()){  // set lower-key node as root
				son = root;
				root = this;
			}

			if (root.getChild() != null){  // add as sibling of current sons
				root.getChild().addNext(son);
			}
			else {
				root.setRank(1);
				son.setParent(root);
			}
			root.setChild(son);

			HeapNode par = root.getParent();
			while (par != null){  // update ranks of all ancestors
				par.increaseRank();
				par = par.getParent();
			}
			return root;
		}

		/**
		 * getters
		 **/
		protected int getKey(){
			return this.item.key;
		}
		protected HeapItem getItem(){
			return this.item;
		}
		protected HeapNode getNext(){
			return this.next;
		}
		protected HeapNode getParent(){
			return this.parent;
		}
		protected HeapNode getChild(){
			return this.child;
		}
		protected int getRank(){
			return this.rank;
		}

		/**
		 * setters
		 **/
		protected void setItem(HeapItem item){
			this.item = item;
		}
		protected void setChild(HeapNode child){
			this.child = child;
		}
		protected void setNext(HeapNode node){
			this.next = node;
		}
		protected void setParent(HeapNode par){
			this.parent = par;
		}
		protected void setRank(int rank){
			this.rank = rank;
		}
		protected void increaseRank(){
			this.rank++;
		}

		@Override
		public String toString() {
			return toString("");
		}
		public String toString(String indent) {
			StringBuilder rep = new StringBuilder(indent);
			rep.append("* * * * * *").append(System.lineSeparator());
			rep.append(String.format("%s%s%s%s", indent, getItem(), System.lineSeparator(), indent));
			rep.append((getNext() != this) ? String.format(" next: %d ", getNext().getKey()) : " self-loop");
			if (getParent() != null) {
				rep.append(String.format("%s%s parent: %d", System.lineSeparator(), indent, getParent().getKey()));
			}
			if (getChild() != null) {
				rep.append(String.format("%s%s child:%d ",System.lineSeparator(), indent, getChild().getKey()));
			}
			rep.append(System.lineSeparator()).append(String.format("%s* * * * * *", indent));
			return rep.toString();
		}

	}

	/**
	 * Class implementing an item in a Binomial Heap.
	 *
	 */
	public class HeapItem{
		public HeapNode node;
		public int key;
		public String info;

		/**
		 * constructors
		 */
		public HeapItem(){
			this(0, "", new HeapNode());
		}
		public HeapItem(int key, String info) {
			this(key, info, new HeapNode());
		}
		public HeapItem(int key, String info, HeapNode node){
			this.key = key;
			this.info = info;
			this.node = node;
			node.item = this;
		}

		/**
		 * getters & setters
		 **/
		protected HeapNode getNode(){
			return this.node;
		}
		protected void setNode(HeapNode node){
			this.node = node;
		}
		protected int getKey(){
			return this.key;
		}
		protected void decKey(int delta){
			this.key -= delta;
		}

		@Override
		public String toString(){
			String rep = " " + this.key + " ,rank"+this.node.getRank();
			if (info != null){
				rep += ", info: "+this.info;
			}
			return "["+rep+"]";
		}
	}

}

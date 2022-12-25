public class Step {
	protected V point;		        // point of interest visited on this path
	protected int coveredDistance;  // covered distance from the start to this point

	Step(V point, int coveredDistance){
		this.point = point;
		this.coveredDistance = coveredDistance;
	}
}

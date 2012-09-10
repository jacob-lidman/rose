#include <stdlib.h>
#include <limits.h>
#include "rose.h"
#include "Transform/ft_transform.h"

int main(int argc, char *argv[]) {
     SgProject *project = frontend(argc, argv);
     ROSE_ASSERT(project != NULL);             

     FT::Transform::ControlStruct *fCS = 
		new FT::Transform::ControlStruct_Composition(
			new FT::Transform::ControlStruct_RedundantExec( (unsigned int) 2),
			new FT::Transform::ControlStruct_Check(
				new FT::Transform::ControlStruct_Composition(
					new FT::Transform::ControlStruct_RedundantExec(0.5),
					new FT::Transform::ControlStruct_Adjudicator(new FT::Transform::Adjucator_Voting_Mean()) )));

     FT::Transform f;
     try {
          f.transformMulti(*fCS, project);
     } catch(FT::Common::FTException &e) {
          cout << "FTException occured: " << e.what() << endl;
          return 1;
     }

     return backend(project);
}

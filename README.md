# CS-5990_PCG_Project
Java implementation of Jim Whitehead's procedural dungeon generation algorithm.
* [Whitehead's code](https://github.com/JimWhiteheadUCSC/smt_dungeon)
* [Whitehead's paper](https://dl.acm.org/doi/10.1145/3402942.3409603)

# How to Run
* Download Java 11.0.2 or later
  * Oracle: (https://www.oracle.com/java/technologies/javase/jdk11-archive-downloads.html)
  * OpenJDK (https://jdk.java.net/archive/)
* Download Z3 library
  * Choose approprite binary for your OS https://github.com/Z3Prover/z3/releases/tag/z3-4.12.1
* Set environment variables
  * Windows
    * Add C:\Program Files\Java\jdk-**"version"**\bin to PATH
    * Add C:\\**"path to z3 folder"**\bin to PATH
    * Add C:\\**"path to z3 folder"**\include to PATH
    * Add C:\Program Files\Java\jdk-**"version"** to JAVA_HOME
* Download JavaFX sdk (https://gluonhq.com/products/javafx/)
* Download jar file from GitHub repository
* Navigate to the directory containing dungeon-smt.jar and run the following command:
  * java -jar --module-path C:\\**“path to”**\javafx-sdk-**“version”**\lib --add-modules=javafx.controls dungeon-smt.jar

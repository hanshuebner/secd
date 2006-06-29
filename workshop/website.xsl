<?xml version="1.0" encoding="iso-8859-1" ?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.0">

 <xsl:output method="html" indent="yes" omit-xml-declaration="yes" doctype-public="-//W3C//DTD HTML 4.0 Strict//EN" />

 <xsl:param name="mode">xml</xsl:param>

 <xsl:template match="/page">

  <html
   xmlns="http://www.w3.org/1999/xhtml">
    <head>
      <title>ECOOP06 LISP Workshop - Reclaim the Hardware Design Space! - <xsl:value-of select="@name"/></title>
      <link rel="stylesheet" type="text/css" href="styles.css" />
      <script src="javascript.js" language="javascript" type="text/javascript"> </script>
    </head>
  
    <body>
      <div id="banner">
        <div id="title">ECOOP06 LISP Workshop<br/>Reclaim the Hardware Design Space!</div>
        <div id="logo">
          <a href="/home">
  	  <img width="75" height="75" alt="BKNR Logo" src="cons-chip.jpg" border="0" />
  	</a>
        </div>
      </div>
      <div id="body">
        <div id="system-column">
          <xsl:call-template name="menu">
            <xsl:with-param name="current" select="@name"/>
          </xsl:call-template>
        </div>
        <div id="content">
          <h1><xsl:value-of select="@title"/></h1>
          <xsl:if test="@author != ''">
           <h2>
            <xsl:choose>
             <xsl:when test="@email != ''">
              <a href="mailto:{@email}"><xsl:value-of select="@author"/></a>
             </xsl:when>
             <xsl:otherwise>
              <a href="mailto:{@email}"><xsl:value-of select="@author"/></a>
             </xsl:otherwise>
            </xsl:choose>
           </h2>
          </xsl:if>
          <xsl:apply-templates/>
        </div>
      </div>
    </body>
  </html>
 </xsl:template>

 <xsl:template match="links">
  <xsl:apply-templates/>
 </xsl:template>

 <xsl:template match="group">
  <h2><xsl:value-of select="@name"/></h2>
  <ul>
   <xsl:apply-templates/>
  </ul>
 </xsl:template>

 <xsl:template match="link">
  <li><a href="{@href}" target="_new"><xsl:value-of select="@title"/></a><xsl:apply-templates/></li>
 </xsl:template>

 <xsl:template match="book">
  <li>
   <i><xsl:value-of select="@author"/>, <strong><xsl:value-of select="@title"/></strong> (<xsl:value-of select="@year"/>, ISBN <xsl:value-of select="@isbn"/>)</i><br/>
   <xsl:apply-templates/>
  </li>
 </xsl:template>  

 <xsl:template match="*">
  <xsl:copy-of select="." />
 </xsl:template>

 <xsl:template name="menu">
  <xsl:param name="current"/>
  <div class="site-menu">
   <xsl:for-each select="document('menu.xml')/menu/item">
    <xsl:choose>
     <xsl:when test="@url = $current">
      <div class="site-menu-active">
       <xsl:value-of select="@title"/>
      </div>
     </xsl:when>
     <xsl:otherwise>
      <div class="site-menu-inactive">
       <a href="{@url}.{$mode}"><xsl:value-of select="@title"/></a>
      </div>
     </xsl:otherwise>
    </xsl:choose>
   </xsl:for-each>
 </div>
 </xsl:template>

</xsl:stylesheet>
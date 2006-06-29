<?xml version="1.0"?>
<xslt:transform  version="1.0" xmlns:xslt="http://www.w3.org/1999/XSL/Transform">
<xslt:output method="html" version="4.01" />
<xslt:variable name="show_type" select="boolean(//header[@type='yes'])"/>
<xslt:variable name="show_summary" select="boolean(//header[@omit-summary!='yes'])"/>
<xslt:variable name="type" select="boolean(//header[@type='yes'])"/>
<xslt:variable name="toggle_type" select="//header[@toggle-type!=0]"/>
<xslt:variable name="show_toggled" select="//header[@signal-type='all']"/>
<xslt:template match="*">
	<xslt:apply-templates/>
</xslt:template>
<xslt:template match="/">
<html>
<head>
	<title>The Toggle Coverage information</title>
	<style>
		aligned-text{
			 text-align	:center
		}
		table-style{
			;width	: 80%
			;background-color: rgb(240,240,240)
		}
		HR{
			;height:1px
			;color:rgb(180,190,210)
		}
		H2{
			;color:rgb(40,40,60)
			;font-style:italic
		}
		H3{
			;color:rgb(50,50,70)
		}
		BODY{
			;color:rgb(40,40,40)
		}
	</style>
	<script type="text/javascript">
		function makeZebra(){
			var i = document.all.oResultTable.tBodies[0].rows.length
			var rows = document.all.oResultTable.tBodies[0].rows
			while(i){
				i--
				rows[i].style.backgroundColor 
					= 
						i%2
						?
							"rgb(245,245,245)"
						:
							"rgb(250,250,250)"
			}
		}			
	</script>
</head>
	<body
		style="
			 background-color		: rgb(245,245,245)
			;scrollbar-base-color	: rgb(245,245,245)
			;scrollbar-darkshadow-color	:rgb(245,245,245)
			;scrollbar-face-color	: rgb(245,245,245)
			;scrollbar-highlight-color	:rgb(245,245,245)
			;scrollbar-shadow-color	: rgb(245,245,245)
			;scrollbar-track-color	: rgb(245,245,245)
			;scrollbar-arrow-color	: rgb(245,245,245)
			
		"
		onLoad = "makeZebra()"
	>
		<div style="
				 text-align:center
				;font-size: 800%
				;z-index: -1
				;position: absolute
				;width	: 80%
				;height	: 90%
				;top	: 5%
				;left	: 10%
		">The Toggle Coverage</div>
		<div
			style = "
				  position	:absolute
				 ;left		: 10%
				 ;top		: 1%
				 ;width		: 85%
				 ;height	: 98%
				 ;border	: 1px solid rgb(150,150,150)
				 ;cursor	: default
				 ;background-color: white
				 ;text-align	: center
				 ;overflow-y	: scroll
				 ;scrollbar-face-color	: rgb(255,255,255)
				 ;;scrollbar-arrow-color: rgb(100,100,100)
				 ;scrollbar-base-color	:rgb(230,230,230)
				 ;scrollbar-shadow-color:rgb(230,230,230)
				 ;filter	: Alpha(Opacity=95)
			"
		>
				<!--center-->
				<h1>The Toggle Coverage Report</h1>
				<h2>Parameters</h2>
				<xslt:call-template name="header"/>
				<br/>
				<hr/>
				<xslt:call-template name="summary-maker"/>
				<h2>Statistics</h2>
				<table style="width:90%;" id="oResultTable">
					<thead>
						<tr>
							<td style="width:60%;text-align:left;"><h3>Signal Name</h3></td>
							<xslt:if test="$type">
								<td style="width:35%;text-align:left;"><h3>Type</h3></td>
							</xslt:if>
							<xslt:if test="$show_toggled">
								<td style="width:15%;text-align:center;"><h3>Covered</h3></td>
							</xslt:if>
							<xslt:choose>
								<xslt:when test="//header[@toggle-type=1] or //header[@toggle-type=2]">
									<td><h3>Negedges</h3></td>
									<td><h3>Posedges</h3></td>
								</xslt:when>
								<xslt:when test="//header[@toggle-type=3]">
									<td><h3>"0" assigns</h3></td>
									<td><h3>"1" assigns</h3></td>
								</xslt:when>
							</xslt:choose>
						</tr>
					</thead>
					<tbody>
						<xslt:apply-templates/>
					</tbody>
				</table>
				<br/>
			<!--/center-->
		</div>
	</body>
</html>
</xslt:template>
<xslt:template name="header">
	<xslt:if test="$show_summary">
		<div
			style = "
 					 background-color:rgb(255,255,245)
					;border		: 1px solid rgb(255,200,150)
			"
		>
		<table style="width:80%;">
			<thead>
				<tr>
					<td style="width:60%"><h3>Switch name</h3></td>
					<td><h3>Value</h3></td>
				</tr>
		</thead>
		<tbody>
			<tr>
				<td>-toggle_type</td>
				<td>
					<xslt:choose>
						<xslt:when test="//header[@toggle-type = '0']"><xslt:text>init</xslt:text></xslt:when>
						<xslt:when test="//header[@toggle-type = '1']"><xslt:text>full</xslt:text></xslt:when>
						<xslt:when test="//header[@toggle-type = '2']"><xslt:text>activity</xslt:text></xslt:when>
						<xslt:otherwise><xslt:text>assign</xslt:text></xslt:otherwise>
					</xslt:choose>
				</td>
			</tr>
			<tr>
				<td>-results</td>
				<td>
					<xslt:choose>
						<xslt:when test="//header[@edge = '0']"><xslt:text>nosingle_edge</xslt:text></xslt:when>
						<xslt:when test="//header[@edge = '1']"><xslt:text>single_edge</xslt:text></xslt:when>
						<xslt:otherwise><xslt:text>undefined</xslt:text></xslt:otherwise>
					</xslt:choose>
				</td>
			</tr>
			<xslt:if test="//header[@project-language = '1']">
				<tr>
					<td>-posedge</td>
					<td><xslt:value-of select="//header/@posedge"/></td>
				</tr>
				<tr>
					<td>-negedge</td>
					<td><xslt:value-of select="//header/@negedge"/></td>
				</tr>
			</xslt:if>
			<tr>
				<td>report name:</td>
				<td><a><xslt:attribute name="href"><xslt:value-of select="//header/@out-file"/></xslt:attribute><xslt:value-of select="//header/@out-file"/></a></td>
			</tr>
			<tr>
				<td>directory:</td>
				<td><a><xslt:attribute name="href">./../<xslt:value-of select="//header/@out-dir"/></xslt:attribute><xslt:value-of select="//header/@out-dir"/></a></td>
			</tr>
			<xslt:if test="//header[@type='yes']">
				<tr>
					<td>-type</td>
					<td/>
			</tr>
			</xslt:if>
			<tr>
				<td>-report</td>
				<td><xslt:value-of select="//header/@signal-type"/></td>
			</tr>
			<tr>
				<td>-unknown_edge</td>
				<td><xslt:value-of select="//header/@unknown-edge"/></td>
			</tr>
		</tbody>
	</table>
	</div>
	</xslt:if>
</xslt:template>
<xslt:template name="decorator">
	<xslt:param name="decor_type"/>
	<xslt:attribute name="style">
		<xslt:choose>
			<xslt:when test='$decor_type="0"'>background-color:red;color:white;</xslt:when>
			<xslt:otherwise>background-color:green;color:yellow;</xslt:otherwise>
		</xslt:choose>
		<xslt:text>text-align:center;</xslt:text>
	</xslt:attribute>
	<xslt:choose>
		<xslt:when test='$decor_type="0"'>NO</xslt:when>
		<xslt:otherwise>YES</xslt:otherwise>
	</xslt:choose>
</xslt:template>
<xslt:template name="index-maker">
	<xslt:param name="signal"/>
	[<xslt:value-of select="$signal/info/@start-index"/> : <xslt:choose>
		<xslt:when test="$signal/info[@inc='yes']"><xslt:value-of select="number(./info/@start-index)+string-length(string(./@value))-1"/></xslt:when>
		<xslt:otherwise><xslt:value-of select="number($signal/info/@start-index)-string-length(string($signal/@value))+1"/></xslt:otherwise>
	</xslt:choose>]
</xslt:template>
<xslt:template match="sig[@type='bit']">
	<xslt:choose>
		<xslt:when test="//header[@signal-type='all']">
			<xslt:call-template name="bit-header">
				<xslt:with-param name="bit_node" select="."/>
			</xslt:call-template>
		</xslt:when>
		<xslt:when test="//header[@signal-type='not_toggled']">
			<xslt:call-template name="bit-header">
				<xslt:with-param name="bit_node" select="."/>
			</xslt:call-template>
		</xslt:when>
		<xslt:otherwise>
			<xslt:call-template name="bit-header">
				<xslt:with-param name="bit_node" select="."/>
			</xslt:call-template>
		</xslt:otherwise>
	</xslt:choose>	
</xslt:template>
<xslt:template name="bit-header">
	<xslt:param name="bit_node"></xslt:param>
	<tr>
		<td><xslt:value-of select="$bit_node/@name"/></td>
		<xslt:if test="$type">
			<td style="aligned-text">
				<xslt:value-of select="$bit_node/@type-info"/>
			</td>
		</xslt:if>
		<xslt:if test="$show_toggled">
			<td style="text-align:center;">
				<xslt:call-template name="decorator">
					<xslt:with-param name="decor_type" select="$bit_node/@value"/>
				</xslt:call-template>
			</td>
		</xslt:if>
		<xslt:if test="//header[@toggle-type!=0]">
			<td>
				<xslt:attribute name="style">
					<xslt:text>text-align:center;</xslt:text>
				</xslt:attribute>
				<xslt:value-of select="$bit_node/i/@the_0"/>
			</td>
			<td>
				<xslt:attribute name="style">
					<xslt:text>text-align:center;</xslt:text>
				</xslt:attribute>
				<xslt:value-of select="$bit_node/i/@the_1"/>
			</td>
		</xslt:if>
	</tr>
</xslt:template>
<xslt:template match="sig[@type='vector']">
	<xslt:choose>
		<xslt:when test="//header[@toggle-type='0']">
			<tr>
				<td><xslt:value-of select="@name"/><xslt:call-template name="index-maker"><xslt:with-param name="signal" select="."/></xslt:call-template></td>
				<xslt:if test="$type">
					<td>
						<xslt:value-of select="./@type-info"/>
					</td>
				</xslt:if>
				<xslt:if test="$show_toggled">
					<td>
						<xslt:choose>
							<xslt:when test="contains(string(./@value),'0')">
								<xslt:call-template name="decorator">
									<xslt:with-param name="decor_type" select="0"/>
								</xslt:call-template>	
							</xslt:when>
							<xslt:otherwise>
								<xslt:call-template name="decorator">
									<xslt:with-param name="decor_type" select="1"/>
								</xslt:call-template>
							</xslt:otherwise>	
						</xslt:choose>
					</td>
				</xslt:if>
			</tr>
		</xslt:when>
		<xslt:otherwise>
			<xslt:choose>
				<xslt:when test="//header[@signal-type='all']">
					<xslt:call-template name="vector-header">
						<xslt:with-param name="vector_node" select="."/> 
					</xslt:call-template>					
				</xslt:when>
				<xslt:when test="//header[@signal-type='not_toggled']">
					<xslt:if test="contains(@value,'0')">
						<xslt:call-template name="vector-header">
							<xslt:with-param name="vector_node" select="."/> 
						</xslt:call-template>
					</xslt:if>
				</xslt:when>
				<xslt:otherwise>
					<xslt:if test="not(contains(@value,'0'))">
						<xslt:call-template name="vector-header">
							<xslt:with-param name="vector_node" select="."/> 
						</xslt:call-template>
					</xslt:if>
				</xslt:otherwise>
			</xslt:choose>
		</xslt:otherwise>
	</xslt:choose>
</xslt:template>
<xslt:template name="vector-header">
	<xslt:param name="vector_node"></xslt:param>
	<tr>
		<td><xslt:value-of select="$vector_node/@name"/></td>
		<xslt:if test="$type">
			<td>
				<xslt:value-of select="$vector_node/@type-info"/>
			</td>
		</xslt:if>
		<td></td>
		<xslt:if test="$toggle_type"><td/><td/></xslt:if>
	</tr>
	<xslt:call-template name="vector-reader">
		<xslt:with-param name="cortage" select="$vector_node/@value"/>
		<xslt:with-param name="index" select="number($vector_node/info/@start-index)"/>
		<xslt:with-param name="inc">
			<xslt:choose>
				<xslt:when test="string($vector_node/info/@inc)='yes'"><xslt:value-of select="number(1)"/></xslt:when>
				<xslt:otherwise><xslt:value-of select="number(-1)"/></xslt:otherwise>
			</xslt:choose>
		</xslt:with-param>
	</xslt:call-template>
</xslt:template>
<xslt:template name="vector-reader">
	<xslt:param name="cortage"/>
	<xslt:param name="index"/>
	<xslt:param name="inc"/>
	<xslt:param name="child" select="number(1)"/>
	<xslt:variable name="toggled" select="substring($cortage,1,1)"/>
	<tr>
		<td>
			<xslt:attribute name="style">
				<xslt:text>text-align:center;</xslt:text>
			</xslt:attribute>
			[<xslt:value-of select="$index"/>]
		</td>
		<xslt:if test="$type">
			<td/>
		</xslt:if>
		<xslt:if test="$show_toggled">
			<td>
				<xslt:call-template name="decorator">
					<xslt:with-param name="decor_type" select="$toggled"/>
				</xslt:call-template>
			</td>
		</xslt:if>
		<xslt:if test="$toggle_type">
			<td>
				<xslt:attribute name="style">
					<xslt:text>text-align:center;</xslt:text>
				</xslt:attribute>
				<xslt:value-of select="./i[$child]/@the_0"/>
			</td>
			<td>
				<xslt:attribute name="style">
					<xslt:text>text-align:center;</xslt:text>
				</xslt:attribute>
				<xslt:value-of select="./i[$child]/@the_1"/>
			</td>
		</xslt:if>
	</tr>
	<xslt:variable name="next" select="substring($cortage,2)"/>
	<xslt:if test="string-length($next)&gt;0">
		<xslt:call-template name="vector-reader">
			<xslt:with-param name="cortage" select="$next"/>
			<xslt:with-param name="inc" select="$inc"/>
			<xslt:with-param name="index" select="$index+$inc"/>
			<xslt:with-param name="child" select="$child+1"/>
		</xslt:call-template>	
	</xslt:if>
</xslt:template>

<xslt:template name="summary-maker">

	<xslt:param name="node_index" select="count(//sig)"/>
	<xslt:param name="total" select="number(0)"/>
	<xslt:param name="toggled" select="number(0)"/>

	<xslt:if test="//header[@omit-summary='no'] and //header[@signal-type='all']">	
		<xslt:choose>
		<xslt:when test="0=$node_index">
			<xslt:variable name="not_toggled" select="number($total)-number($toggled)"/>
			
			<h2>Summary</h2>
			<table style="width:80%;">
				<thead>
					<tr>
						<td style="width:10%"></td>
						<td style="width:40%"></td>
						<td style="width:40%"></td>
						<td style="width:10%"></td>
					</tr>
				</thead>
				<tbody>
					<tr>
						<td style="width:10%"></td>
						<td style="width:40%">All:</td>
						<td style="width:40%">
							<xslt:value-of select="$total"/><xslt:text>	</xslt:text>(100%)
						</td>
						<td style="width:10%"></td>
					</tr>
					<tr>
						<td style="width:10%"></td>
						<td style="width:40%">Toggled:</td>
						<td style="width:40%">
							<xslt:value-of select="$toggled"/><xslt:text> </xslt:text><xslt:value-of select="format-number(number($toggled) div number($total),'(###.##%)')"/>
						</td>
						<td style="width:10%"></td>
					</tr>
					<tr>
						<td style="width:10%"></td>
						<td style="width:40%">Not toggled:</td>
						<td style="width:40%">
							<xslt:value-of select="$not_toggled"/><xslt:text> </xslt:text><xslt:value-of select="format-number(number($not_toggled) div number($total),'(###.##%)')"/>
						</td>
						<td style="width:10%"></td>
					</tr>
				</tbody>
			</table>
			<br/>
			<hr/>
		</xslt:when>
		<xslt:otherwise>
			<xslt:variable name="new-node_index" select="$node_index - 1"/>
			<xslt:variable name="new-total">
				<xslt:choose>
						<xslt:when test="//header[@toggle-type='0']">
							<xslt:value-of select="$total+1"/>
						</xslt:when>
						<xslt:otherwise>
							<xslt:value-of select="$total + string-length((//sig/@value)[$node_index])"/>
						</xslt:otherwise>
					</xslt:choose>
			</xslt:variable>
			<xslt:variable name="new-toggled">
				<xslt:choose>
						<xslt:when test="//header[@toggle-type='0']">
							<xslt:choose>
								<xslt:when test="false=contains(string((//sig/@value)[$node_index]),'0')">
									<xslt:value-of select="$toggled + 1"/>
								</xslt:when>
								<xslt:otherwise>
									<xslt:value-of select="$toggled"/>
								</xslt:otherwise>
							</xslt:choose>
						</xslt:when>
						<xslt:otherwise>
							<xslt:value-of select="$toggled+string-length(translate(string((//sig/@value)[$node_index]),'0',''))"/>
						</xslt:otherwise>
					</xslt:choose>
			</xslt:variable>
			<xslt:call-template name="summary-maker">
				<xslt:with-param name="node_index" select="$new-node_index"/>
				<xslt:with-param name="total" select="$new-total"/>
				<xslt:with-param name="toggled" select="$new-toggled"/>
			</xslt:call-template>
		</xslt:otherwise>
	</xslt:choose>
	</xslt:if>
	
</xslt:template>

<xslt:template match="mem">
    <tr>
        <td>
            <xslt:value-of select="./@name"/>
            <xslt:if test="not($type)">
                <xslt:text> [</xslt:text><xslt:value-of select="./info/@width-left"/> : <xslt:value-of select="./info/@width-right"/><xslt:text>]</xslt:text>
                <xslt:text> [</xslt:text><xslt:value-of select="./info/@depth-left"/> : <xslt:value-of select="./info/@depth-right"/><xslt:text>]</xslt:text>
            </xslt:if>
        </td>
        <xslt:if test="$type">
            <td>
                <xslt:value-of select="./@type-info"/>
            </td>
        </xslt:if>
        <xslt:if test="$show_toggled">
            <td/>
        </xslt:if>
        <xslt:if test="$toggle_type">
            <td/><td/>
        </xslt:if>
    </tr>
    <xslt:call-template   name="memory-parser">
        <xslt:with-param name="node"   select="."/>
        <xslt:with-param name="index-depth-left" select="./info/@depth-left"/>
        <xslt:with-param name="index-depth-right" select="./info/@depth-right"/>
        <xslt:with-param name="index-width-left" select="./info/@width-left"/>
        <xslt:with-param name="index-width-right" select="./info/@width-right"/>
    </xslt:call-template>
</xslt:template>

<xslt:template name="memory-parser">
    <xslt:param    name="node"/>
    <xslt:param    name="index"    select="number(1)"/>
    <xslt:param    name="index-depth-left"    select="/.."/>
    <xslt:param    name="index-depth-right"   select="/.."/>
    <xslt:param    name="index-width-left"    select="/.."/>
    <xslt:param    name="index-width-right"   select="/.."/>

        <xslt:choose>
            <xslt:when test="not($toggle_type)">
                <tr>
                <xslt:variable name="isToggled" select="not(contains($node[$index]/sig/@value,'0'))"/>
                <xslt:choose>
                        <xslt:when test="//header[@signal-type='all']">
                                <xslt:call-template name="memory-vector-header">
                                        <xslt:with-param name="vector_node" select="."/>
                                        <xslt:with-param name="depth-index" select="$index-depth-left"/>
                                </xslt:call-template>					
                        </xslt:when>
                        <xslt:when test="//header[@signal-type='not_toggled']">
                                <xslt:if test="not($isToggled)">
                                        <xslt:call-template name="memory-vector-header">
                                                <xslt:with-param name="vector_node" select="."/>
                                                <xslt:with-param name="depth-index" select="$index-depth-left"/>
                                        </xslt:call-template>
                                </xslt:if>
                        </xslt:when>
                        <xslt:otherwise>
                                <xslt:if test="$isToggled">
                                        <xslt:call-template name="memory-vector-header">
                                                <xslt:with-param name="vector_node" select="."/>
                                                <xslt:with-param name="depth-index" select="$index-depth-left"/>
                                        </xslt:call-template>
                                </xslt:if>
                        </xslt:otherwise>
                </xslt:choose>
                </tr>
            </xslt:when>
            <xslt:otherwise>
                <xslt:call-template name="word-parser">
                    <xslt:with-param name="node" select="($node/sig)[$index]"/>
                    <xslt:with-param name="depth-index" select="$index-depth-left"/>
                    <xslt:with-param name="index-width-left" select="$index-width-left"/>
                    <xslt:with-param name="index-width-right" select="$index-width-right"/>
                </xslt:call-template>
            </xslt:otherwise>
        </xslt:choose>
    
    <xslt:if test="$index-depth-left != $index-depth-right">
        <xslt:variable name="next-index" select="$index + 1"/>
        <xslt:variable name="next-index-depth-left">
            <xslt:choose>
                <xslt:when test="$index-depth-left &gt; $index-depth-right">
                    <xslt:value-of select="$index-depth-left - 1"/>
                </xslt:when>
                <xslt:otherwise>
                    <xslt:value-of select="$index-depth-left + 1"/>
                </xslt:otherwise>
            </xslt:choose>
        </xslt:variable>
        
        <xslt:call-template name="memory-parser">
            <xslt:with-param name="node" select="$node"/>
            <xslt:with-param name="index" select="$next-index"/>
            <xslt:with-param name="index-depth-left" select="$next-index-depth-left"/>
            <xslt:with-param name="index-depth-right" select="$index-depth-right"/>
            <xslt:with-param name="index-width-left" select="$index-width-left"/>
            <xslt:with-param name="index-width-right" select="$index-width-right"/>
        </xslt:call-template>
    </xslt:if>
</xslt:template>

<xslt:template name="word-parser">
    <xslt:param name="node"/>
    <xslt:param name="index" select="number(1)"/>
    <xslt:param name="depth-index"/>
    <xslt:param name="index-width-left"/>
    <xslt:param name="index-width-right"/>
    
    <xslt:variable name="isToggled" select="substring(($node/i)[$index]/@value,$index,1)='1'"/>
    
    <xslt:choose>
        <xslt:when test="//header[@signal-type='all']">
            <tr>
                <xslt:call-template name="memory-vector-header">
                    <xslt:with-param name="node" select="($node/i)[$index]"/>
                    <xslt:with-param name="isToggled" select="$isToggled"/>
                    <xslt:with-param name="depth-index" select="$depth-index"/>
                    <xslt:with-param name="width-index" select="$index-width-left"/>
                </xslt:call-template>
            </tr>
        </xslt:when>
        <xslt:when test="//header[@signal-type='toggled']">
            <xslt:if test="$isToggled">
                <tr>
                    <xslt:call-template name="memory-vector-header">
                        <xslt:with-param name="node" select="($node/i)[$index]"/>
                        <xslt:with-param name="isToggled" select="$isToggled"/>
                        <xslt:with-param name="depth-index" select="$depth-index"/>
                        <xslt:with-param name="width-index" select="$index-width-left"/>
                    </xslt:call-template>
                </tr>
            </xslt:if>
        </xslt:when>
        <xslt:otherwise>
            <xslt:if test="not($isToggled)">
                <tr>
                    <xslt:call-template name="memory-vector-header">
                        <xslt:with-param name="node" select="($node/i)[$index]"/>
                        <xslt:with-param name="isToggled" select="$isToggled"/>
                        <xslt:with-param name="depth-index" select="$depth-index"/>
                        <xslt:with-param name="width-index" select="$index-width-left"/>
                    </xslt:call-template>
                </tr>
            </xslt:if>
        </xslt:otherwise>
    </xslt:choose>
    
    <xslt:if test="$index-width-left != $index-width-right">
        <xslt:variable name="next-index-width-index">
            <xslt:choose>
                <xslt:when test="$index-width-left &gt; $index-width-right">
                    <xslt:value-of select="$index-width-left - 1"/>
                </xslt:when>
                <xslt:otherwise>
                    <xslt:value-of select="$index-width-left + 1"/>
                </xslt:otherwise>
            </xslt:choose>
        </xslt:variable>
        <xslt:variable name="next-index" select="$index + 1"/>
        <xslt:call-template name="word-parser">
            <xslt:with-param name="node" select="$node"/>
            <xslt:with-param name="index" select="$next-index"/>
            <xslt:with-param name="depth-index" select="$depth-index"/>
            <xslt:with-param name="index-width-left" select="$next-index-width-index"/>
            <xslt:with-param name="index-width-right" select="$index-width-right"/>            
        </xslt:call-template>
    </xslt:if>
</xslt:template>

<xslt:template name="memory-vector-header">
    <xslt:param name="node"/>
    <xslt:param name="depth-index"/>
    <xslt:param name="width-index"/>
    <xslt:param name="isToggled"/>
    <td>
        <xslt:attribute name="style">
	    <xslt:text>text-align:center;</xslt:text>
	</xslt:attribute>
        <xslt:text>    [</xslt:text><xslt:value-of select="$depth-index"/><xslt:text>]</xslt:text>
        <xslt:if test="$toggle_type">
            <xslt:text>[</xslt:text><xslt:value-of select="$width-index"/><xslt:text>]</xslt:text>
        </xslt:if>
    </td>
    <xslt:if test="$show_type">
        <td/>
    </xslt:if>
    <xslt:if test="//header[@signal-type='all']">
        <td>
            <xslt:call-template name="decorator">
                    <xslt:with-param name="decor_type">
                        <xslt:choose>
                            <xslt:when test="isToggled">
                                <xslt:value-of select="'1'"/>
                            </xslt:when>
                            <xslt:otherwise>
                                <xslt:value-of select="'0'"/>
                            </xslt:otherwise>
                        </xslt:choose>
                    </xslt:with-param>
            </xslt:call-template>
        </td>
    </xslt:if>
    <xslt:if test="$toggle_type">
        <td style="text-align:center;"><xslt:value-of select="$node/@the_0"/></td>
        <td style="text-align:center;"><xslt:value-of select="$node/@the_1"/></td>
    </xslt:if>    
</xslt:template>

</xslt:transform>
